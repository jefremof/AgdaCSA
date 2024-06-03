{-# OPTIONS --safe #-}

module isa where

open import Data.Bool.Base using (if_then_else_)
open import Data.Char.Base using (Char)
open import Data.Fin.Base using (Fin ; fromℕ<)
open import Data.Nat.Base
open import Data.Nat.Properties using (_<?_)
open import Data.Maybe.Base hiding (map)
open import Data.Product.Base using (_×_)
open import Data.String.Base using (String ; _++_ ; toList ; fromList ; words)
open import Data.List.Base hiding (_++_ ; map ; filter)
open import Data.Vec.Base as Vec using (Vec ; _∷_ ; [] ; map ; countᵇ)
open import Data.Vec using (filter)
open import Function.Base using (case_of_ ; _∘_)
open import Relation.Nullary.Decidable as Dec using (yes; no)

------------------------------------------------------------------------
-- ISA

data Opcode : Set where
  RIGHT LEFT DEC INC PRINT INPUT JMP JZ HLT : Opcode

Optype = ℕ
CONTROL-FLOW   = 1
ADDRESS-SHIFT  = 2
MEMORY-WRITING = 3
GENERAL        = 4

type : Opcode → Optype
type LEFT  = ADDRESS-SHIFT
type RIGHT = ADDRESS-SHIFT
type JMP   = CONTROL-FLOW
type JZ    = CONTROL-FLOW
type HLT   = GENERAL
type INPUT = MEMORY-WRITING
type INC   = MEMORY-WRITING
type DEC   = MEMORY-WRITING
type PRINT = GENERAL

data Operation (n : ℕ) : Opcode → Optype → Set where
  right :         Operation n RIGHT ADDRESS-SHIFT
  left  :         Operation n LEFT  ADDRESS-SHIFT
  dec   :         Operation n DEC   MEMORY-WRITING
  inc   :         Operation n INC   MEMORY-WRITING
  input :         Operation n INPUT MEMORY-WRITING
  print :         Operation n PRINT GENERAL
  jmp   : Fin n → Operation n JMP   CONTROL-FLOW
  jz    : Fin n → Operation n JZ    CONTROL-FLOW
  hlt   :         Operation n HLT   GENERAL 

record Instr (n : ℕ) : Set where
  constructor _,_,_
  field
    {term}    : String
    opcode    : Opcode
    optype    : Optype
    operation : Operation n opcode optype
open Instr

instrBuild : ∀ {n} → String → (opc : Opcode) → Operation n opc (type opc) → Instr n
instrBuild txt opc oper = record
  { term      = txt
  ; opcode    = opc
  ; optype    = type (opc)
  ; operation = oper
  }

instrInit : ∀ {n opcode optype} → Operation n opcode optype → String → Instr n
instrInit right txt   = instrBuild txt RIGHT right 
instrInit left txt    = instrBuild txt LEFT  left
instrInit dec txt     = instrBuild txt DEC   dec
instrInit inc txt     = instrBuild txt INC   inc
instrInit input txt   = instrBuild txt INPUT input
instrInit print txt   = instrBuild txt PRINT print
instrInit (jmp x) txt = instrBuild txt JMP   (jmp x)
instrInit (jz x) txt  = instrBuild txt JZ    (jz x)
instrInit hlt txt     = instrBuild txt HLT   (hlt)

showOpcode : ∀ {n} → Instr n → String
showOpcode instr with opcode instr
... | JMP   = "jmp"
... | JZ    = "jz"
... | PRINT = "print"
... | INPUT = "input"
... | LEFT  = "left"
... | RIGHT = "right"
... | INC   = "increment"
... | DEC   = "decrement"
... | HLT   = "halt"

showInstruction : ∀ {n} → Instr n → String
showInstruction instr = showOpcode instr ++ "  " ++ term instr




------------------------------------------------------------------------
-- Примитивный парсинг Json

cropBrackets : String → List Char
cropBrackets txt with (drop 2 (toList txt))
... | list = (take (length list ∸ 1) list)


splitRecords : ℕ → List Char → List Char → List String
splitRecords _ [] _                       = []
splitRecords 0 _ _                        = []
splitRecords (2+ n) ('}' ∷ xs) buffer = (fromList buffer) ∷ (splitRecords n (drop 2 xs) [])
splitRecords (suc n) (x  ∷  xs) buffer = splitRecords n xs (buffer ∷ʳ x)

parseNonJumpOpcode : ∀ {n} → String → String → Maybe (Instr n)
parseNonJumpOpcode txt "\"right\","     = just (instrInit right txt)
parseNonJumpOpcode txt "\"left\","      = just (instrInit left txt)
parseNonJumpOpcode txt "\"input\","     = just (instrInit input txt)
parseNonJumpOpcode txt "\"print\","     = just (instrInit print txt)
parseNonJumpOpcode txt "\"increment\"," = just (instrInit inc txt)
parseNonJumpOpcode txt "\"decrement\"," = just (instrInit dec txt)
parseNonJumpOpcode _ other       = nothing


parseString : List Char → Maybe ℕ
parseString ('0' ∷ []) = just 0
parseString ('1' ∷ []) = just 1
parseString ('2' ∷ []) = just 2
parseString ('3' ∷ []) = just 3
parseString ('4' ∷ []) = just 4
parseString ('5' ∷ []) = just 5
parseString ('6' ∷ []) = just 6
parseString ('7' ∷ []) = just 7
parseString ('8' ∷ []) = just 8
parseString ('9' ∷ []) = just 9
parseString ('0' ∷ xs) = (parseString xs) >>= λ x → just (x + 0) 
parseString ('1' ∷ xs) = (parseString xs) >>= λ x → just (x + (10 ^ (length xs))) 
parseString ('2' ∷ xs) = (parseString xs) >>= λ x → just (x + (2 * 10 ^ (length xs))) 
parseString ('3' ∷ xs) = (parseString xs) >>= λ x → just (x + (3 * 10 ^ (length xs))) 
parseString ('4' ∷ xs) = (parseString xs) >>= λ x → just (x + (4 * 10 ^ (length xs))) 
parseString ('5' ∷ xs) = (parseString xs) >>= λ x → just (x + (5 * 10 ^ (length xs)))    
parseString ('6' ∷ xs) = (parseString xs) >>= λ x → just (x + (6 * 10 ^ (length xs))) 
parseString ('7' ∷ xs) = (parseString xs) >>= λ x → just (x + (7 * 10 ^ (length xs)))  
parseString ('8' ∷ xs) = (parseString xs) >>= λ x → just (x + (8 * 10 ^ (length xs))) 
parseString ('9' ∷ xs) = (parseString xs) >>= λ x → just (x + (9 * 10 ^ (length xs))) 
parseString _ = nothing

parseInstruction : ∀ {n} → String → Maybe (Instr n)
parseInstruction {n} rec with (words rec)
... | _ ∷ opc ∷ _ ∷ txt ∷ []                    = parseNonJumpOpcode txt opc
... | _ ∷ "\"halt\"" ∷ []                      = just (instrInit hlt "")
... | _ ∷ opc ∷ _ ∷ arg ∷ _ ∷ txt ∷ [] = parseJump n opc txt (toList arg)
  where
  parseJump : ∀ (n) → String → String → List Char → Maybe (Instr n)
  parseJump n opc txt x with (parseString (take (length x ∸ 1) x))
  parseJump n "\"jmp\"," txt _ | (just m) with (m <? n)
  ... | (yes proof) = just (instrInit (jmp (fromℕ< proof)) txt)
  ... | (no _)      = nothing
  parseJump n "\"jmp\"," _ _ | nothing = nothing
  parseJump n "\"jz\"," txt _  | (just m) with (m <? n)
  ... | (yes proof) = just (instrInit (jz (fromℕ< proof)) txt)
  ... | (no _)      = nothing
  parseJump n "\"jz\"," _ _ | nothing = nothing
  parseJump n _ _ _ | _ = nothing
... | _                                         = nothing

parseInstructions : ∀ {n} → Vec String n → Vec (Maybe (Instr n)) n
parseInstructions records = map parseInstruction records

toMaybeVec : {A : Set} (n : ℕ) → Vec (Maybe A) n → Maybe (Vec A n)
toMaybeVec 0 [] = just []
toMaybeVec m (nothing ∷ xs) = nothing
toMaybeVec (suc m) ((just x) ∷ xs) = (toMaybeVec m xs) >>= λ y → just (x ∷ y)

selectExisting : ∀ {n} → Vec (Maybe (Instr n)) n → Maybe (Vec (Instr n) n)
selectExisting {n} instructions = toMaybeVec n instructions

instrVecFromList : (l : List String) → Vec String _
instrVecFromList list = Vec.fromList list

parseJSON1 : String → List String
parseJSON1 txt with (cropBrackets txt)
... | x = splitRecords (length x) x []

parseJSON2 : (ls : List String) → Vec String (length ls)
parseJSON2 txt = Vec.fromList (txt)

parseJSON3 : ∀ {n} → Vec String n → Vec (Maybe (Instr n)) n
parseJSON3 vec = parseInstructions vec

parseJSON = selectExisting ∘ parseJSON3 ∘ parseJSON2 ∘ parseJSON1

