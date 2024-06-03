{-# OPTIONS --guardedness #-}

module translatorInner where

open import Agda.Builtin.Char using (Char; primNatToChar ; primCharToNat)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Sigma using (fst ; snd)
open import Data.Bool.Base
open import Data.Char.Base as Char using (show)
open import Data.Fin.Base hiding (_+_)
open import Data.Fin.Show as Fin
open import Data.List as List using (List; []; _∷_ ; _∷ʳ_ ; length)
open import Data.Maybe as Maybe using (Maybe; just; nothing; is-just) renaming (_>>=_ to _M>>=_)
open import Data.Nat.Base hiding (pred)
open import Data.Nat.Show as ℕ using (show)
open import Data.Nat.Properties using (_<?_ ; _>?_ ; 0<1+n ; m<m+n ; _≟_ ; ≤-pred)
open import Data.Product.Base using (_×_ ; _,′_) 
open import Data.String.Base using (String; wordsBy ; fromList ; _++_ ; toList ; unwords ; unlines)
open import Data.Vec.Base hiding (_++_) renaming (fromList to vecFromList ; toList to vecToList ; _∷ʳ_ to _Vec∷ʳ_)
open import IO
open import Function.Base using (_∘_ ; case_of_ ; _$_ ; _|>_)
open import Relation.Nullary.Decidable as Dec using (yes; no; isYes)
open import System.Exit using (die)
open import Level using (0ℓ)
open import Logging using (log ; debug ; info ; warning)

open import isa
open import machineInner using (Fin-zero-init ; pri)

_inRegularSymbols : Char → Bool
'<' inRegularSymbols = true
'>' inRegularSymbols = true
'-' inRegularSymbols = true
'+' inRegularSymbols = true
'.' inRegularSymbols = true
',' inRegularSymbols = true
_ inRegularSymbols   = false

Term = Char × ℕ × ℕ

toTerm : ℕ → ℕ → Char → Term
toTerm line pos sym = (sym ,′ line ,′ pos)

showTerm : Term → String
showTerm t = "[" ++ ℕ.show (fst (snd t)) ++ "," ++ ℕ.show (snd (snd t)) ++ "," ++ (Char.show (fst t)) ++ "]"


textToTerms : ℕ → List Char → ℕ → ℕ → Maybe (List Term)
--textToTerms n list line pos =
textToTerms 0 _ _ _        = nothing
textToTerms (suc n) [] _ _ = just []
textToTerms (suc n) (x ∷ xs) line pos with x inRegularSymbols
... | true = textToTerms (suc n) xs line (suc pos) M>>= just ∘ ((toTerm line pos x) ∷_)
textToTerms (suc n) ('\n' ∷ xs) line pos | false = textToTerms (suc n) xs (suc line) 0
textToTerms (suc n) ('[' ∷ xs)  line pos | false = textToTerms (2+ n) xs line (suc pos) M>>= just ∘ ((toTerm line pos '[') ∷_)
textToTerms (suc n) (']' ∷ xs)  line pos | false = textToTerms n xs line (suc pos) M>>= just ∘ ((toTerm line pos ']') ∷_)
textToTerms (suc n) (x ∷ xs) line pos | false    = textToTerms (suc n) xs line (suc pos)

updateProgram :  ∀ {n} → Fin (suc n) → Fin (suc n) → String → Vec (Maybe (Instr (suc n))) (suc n) → Vec (Maybe (Instr (suc n))) (suc n)
updateProgram {n} index saved t program with (suc (toℕ index)) <? suc n
... | yes proof = let first      = (program [ index ]≔ just (instrInit (jmp (opposite saved)) t))
                      unfinished = lookup program saved
                  in first [ saved ]≔ (unfinished M>>= λ unf → just (instrInit (jz (opposite (pred (pred (fromℕ< proof))))) (Instr.term unf)))
... | no _ = let first      = (program [ index ]≔ just (instrInit (jmp (opposite saved)) t))
                 unfinished = lookup program saved
             in first [ saved ]≔ (unfinished M>>= λ unf → just (instrInit (jz (fromℕ n)) (Instr.term unf)))

iterateTerms : ∀ {n} → .{{NonZero n}} → Fin n → List Term → List (Fin n) → Vec (Maybe (Instr n)) n → Vec (Maybe (Instr n)) n
iterateTerms (suc i) (x ∷ xs) [] program with (fst x)
... | ']' = iterateTerms (pred (suc i)) xs [] program
... | '+' = iterateTerms (pred (suc i)) xs [] (program [ suc i ]≔ just (instrInit inc (showTerm x)))
... | '-' = iterateTerms (pred (suc i)) xs [] (program [ suc i ]≔ just (instrInit dec (showTerm x)))
... | '<' = iterateTerms (pred (suc i)) xs [] (program [ suc i ]≔ just (instrInit left (showTerm x)))
... | '>' = iterateTerms (pred (suc i)) xs [] (program [ suc i ]≔ just (instrInit right (showTerm x)))
... | '.' = iterateTerms (pred (suc i)) xs [] (program [ suc i ]≔ just (instrInit print (showTerm x)))
... | ',' = iterateTerms (pred (suc i)) xs [] (program [ suc i ]≔ just (instrInit input (showTerm x)))
... | '[' = iterateTerms (pred (suc i)) xs ((suc i) ∷ []) (program [ (suc i) ]≔ just (instrInit (jz zero) (showTerm x)))
... | _   = iterateTerms (pred (suc i)) xs [] program
iterateTerms (suc i) (x ∷ xs) (s ∷ stack) program with (fst x)
... | '+' = iterateTerms (pred (suc i)) xs (s ∷ stack) (program [ suc i ]≔ just (instrInit inc (showTerm x)))
... | '-' = iterateTerms (pred (suc i)) xs (s ∷ stack) (program [ suc i ]≔ just (instrInit dec (showTerm x)))
... | '<' = iterateTerms (pred (suc i)) xs (s ∷ stack) (program [ suc i ]≔ just (instrInit left (showTerm x)))
... | '>' = iterateTerms (pred (suc i)) xs (s ∷ stack) (program [ suc i ]≔ just (instrInit right (showTerm x)))
... | '.' = iterateTerms (pred (suc i)) xs (s ∷ stack) (program [ suc i ]≔ just (instrInit print (showTerm x)))
... | ',' = iterateTerms (pred (suc i)) xs (s ∷ stack) (program [ suc i ]≔ just (instrInit input (showTerm x)))
... | '[' = iterateTerms (pred (suc i)) xs ((suc i) ∷ s ∷ stack) (program [ (suc i) ]≔ just (instrInit (jz zero) (showTerm x)))
... | ']' = iterateTerms (pred (suc i)) xs (stack) (updateProgram (suc i) s (showTerm x) program)
... | _   = iterateTerms (pred (suc i)) xs stack program
iterateTerms zero (x ∷ xs) [] program with (fst x)
... | '+' = program [ zero ]≔ just (instrInit inc (showTerm x))
... | '-' = program [ zero ]≔ just (instrInit dec (showTerm x))
... | '<' = program [ zero ]≔ just (instrInit left (showTerm x))
... | '>' = program [ zero ]≔ just (instrInit right (showTerm x))
... | '.' = program [ zero ]≔ just (instrInit print (showTerm x))
... | ',' = program [ zero ]≔ just (instrInit input (showTerm x))
... | _   = program
iterateTerms zero (x ∷ xs) (s ∷ stack) program with (fst x)
... | ']' = updateProgram zero s (showTerm x) program
... | _   = program
iterateTerms _ [] _ program = program

translate1 : String → IO (List Term)
translate1 text = do
  (just terms) ← pure (textToTerms 1 (toList text) 0 0)
    where nothing → die "Unbalanced brackets"

  pure terms

showEncoded : ∀ {n opcode optype} → String → Operation n opcode optype → String
showEncoded t (jmp x) = "{\"opcode\": \"jmp\", \"arg\": " ++ (Fin.show x) ++ ", \"term\": " ++ t ++ "},"
showEncoded t (jz x)  = "{\"opcode\": \"jz\", \"arg\": " ++ (Fin.show x) ++ ", \"term\": " ++ t ++ "},"
showEncoded t right   = "{\"opcode\": \"right\", \"term\": " ++ t ++ "},"
showEncoded t left    = "{\"opcode\": \"left\", \"term\": " ++ t ++ "},"
showEncoded t dec     = "{\"opcode\": \"decrement\", \"term\": " ++ t ++ "},"
showEncoded t inc     = "{\"opcode\": \"increment\", \"term\": " ++ t ++ "},"
showEncoded t input   = "{\"opcode\": \"input\", \"term\": " ++ t ++ "},"
showEncoded t print   = "{\"opcode\": \"print\", \"term\": " ++ t ++ "},"
showEncoded t hlt     = "{\"opcode\": \"halt\"}]"

encodeInstruction : ∀ {n} → Instr n → String
encodeInstruction instr = showEncoded (Instr.term instr) (Instr.operation instr) 

foldInstruction : ∀ {n} → Instr n → String → String
foldInstruction instr txt = txt ++ (encodeInstruction instr)

translate2 : (ls : List Term) → String → IO _
translate2 terms path = do
  let terms-vec = vecFromList ((toTerm 0 0 '-') ∷ terms)
      terms-num = 1 + List.length terms
      program   : Vec (Maybe (Instr terms-num)) terms-num 
      program =  (just (instrInit hlt "")) ∷ (replicate (List.length terms) nothing) 

  (yes proof) ← pure (terms-num >? 0)
      where (no _) → (die "Invalid program code")

  let maybe-code = (iterateTerms {{>-nonZero proof}} (opposite (Fin-zero-init {{>-nonZero proof}})) terms [] program)

  (just code) ← pure (selectExisting  maybe-code)
    where nothing → (die "Invalid program code")

  let json = (foldr′ foldInstruction "[" code)
  putStrLn json
  writeFile path json

  pure code



translate : String → String → IO _ 
translate txt path = do
  l ← translate1 txt

  ignore (translate2 l path)

