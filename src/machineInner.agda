{-# OPTIONS --guardedness #-}

module machineInner where

open import Agda.Builtin.Char using (Char; primNatToChar ; primCharToNat)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Sigma using (fst ; snd)
open import Data.Bool.Base
open import Data.Char.Base as Char using (show)
open import Data.Fin.Base hiding (_+_)
open import Data.Fin.Show as Fin
open import Data.List as List using (List; []; _∷_ ; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Nat.Base hiding (pred)
open import Data.Nat.Show as ℕ using (show)
open import Data.Nat.Properties using (_<?_ ; _>?_ ; 0<1+n ; m<m+n ; _≟_)
open import Data.Product.Base using (_×_ ; _,′_) 
open import Data.String.Base using (String; wordsBy ; fromList ; _++_ ; toList ; unwords ; unlines)
open import Data.Vec.Base hiding (_++_ ; _∷ʳ_) renaming (fromList to vecFromList ; toList to vecToList)
open import IO
open import Function.Base using (_∘_ ; case_of_ ; _$_ ; _|>_)
open import Relation.Nullary.Decidable as Dec using (yes; no; isYes)
open import System.Exit using (die)
open import Level using (0ℓ)
open import Logging using (log ; debug ; info ; warning)

open import isa 

------------------------------------------------------------------------
-- Вспомогательные функции


-- Инициализировать нулём любой Fin n, где n ≠ 0.
Fin-zero-init : ∀ {n} → .{{NonZero n}} → Fin n
Fin-zero-init {suc n} = fromℕ< 0<1+n


-- Машинное слово - синоним для Fin n
-- Word n - множество значений [0 ; n)
Word = Fin

Word8 = Word 256


-- Инкрементировать и декрементировать машинное слово
word-inc : ∀ {n} → Word n → Word n
word-inc {n} index with suc (toℕ index) <? n
... | no _      = opposite index        -- Переполнение (0)
... | yes proof = fromℕ< proof          -- Следующий индекс

word-dec : ∀ {n} → Word n → Word n
word-dec {n} index  with toℕ index ≡ᵇ 0
... | true  = opposite index            -- Переполнение (n-1)
... | false = pred index                -- Предыдущий индекс


-- Отобразить машинное слово как символ
showWordChar : ∀ {n} → Word n → String
showWordChar = Char.show ∘ primNatToChar ∘ toℕ

-- Преобразовать символ в машинное слово
charToWord : Char → Word8
charToWord char with (primCharToNat char <? 256)
... | yes proof = fromℕ< proof
... | no _      = zero

------------------------------------------------------------------------
-- DataPath

record DataPath : Set where
  constructor DP
  field
    {data-memory-size}    : ℕ
    data-memory           : Vec Word8 data-memory-size
    data-address          : Word data-memory-size
    {input-buffer-length} : ℕ
    input-buffer          : Vec Word8 input-buffer-length
    output-buffer         : List Char
    acc                   : Word8
open DataPath

-- Инициализация начального состояния DataPath
datapathInit : (n : ℕ) → .{{NonZero n}} → {m : ℕ} → Vec Word8 m → DataPath
datapathInit n inbuf = record
  { data-memory   = replicate n zero
  ; data-address  = Fin-zero-init
  ; input-buffer  = inbuf
  ; output-buffer = []
  ; acc           = zero
  }


-- Базовые операции с текущей ячейкой памяти и аккумулятором

writeMemory : Word8 → DataPath → DataPath
writeMemory word old = let mem  = data-memory old
                           addr = data-address old
                        in record old {data-memory = mem [ addr ]≔ word}

readMemory : DataPath → Word8
readMemory datapath = lookup (data-memory datapath) (data-address datapath)


------------------------------------------------------------------------
-- Signals

latch-acc : DataPath → DataPath
latch-acc old = record old {acc = readMemory old}

zero-flag : DataPath → Bool
zero-flag datapath = toℕ (acc datapath) ≡ᵇ 0


signal-output : DataPath → IO DataPath
signal-output old = let buffer = output-buffer old
                        char   = primNatToChar (toℕ $ acc old)
                        msg    = "output: '" ++ (fromList buffer) ++ "' << " ++ Char.show char
                    in debug msg >> pure record old {output-buffer = buffer ∷ʳ char}
                    
latch-data-addr : (op : Opcode) → .{type op ≡ ADDRESS-SHIFT} → DataPath → DataPath
latch-data-addr LEFT old  = record old {data-address = word-dec (data-address old)}
latch-data-addr RIGHT old = record old {data-address = word-inc (data-address old)}

signal-wr : (op : Opcode) → .{type op ≡ MEMORY-WRITING} → DataPath → IO (Maybe DataPath)
signal-wr INC   old = pure (just (writeMemory (word-inc $ acc old) old))
signal-wr DEC   old = pure (just (writeMemory (word-dec $ acc old) old))
signal-wr INPUT old with input-buffer old
... | []     = warning "Input buffer is empty!" >> pure nothing
... | x ∷ xs = debug ("input: " ++ (showWordChar x)) >>
               pure (just (writeMemory x (record old {input-buffer = xs})))


------------------------------------------------------------------------
-- ControlUnit

record ControlUnit : Set where
  constructor CU
  field
    {program-length} : ℕ
    program          : Vec (Instr program-length) program-length
    program-counter  : Word program-length
    tick             : ℕ
open ControlUnit renaming (tick to current-tick)

controlunitInit : ∀ {n} → .{{NonZero n}} → Vec (Instr n) n → ControlUnit
controlunitInit {n} instructions = record
  { program         = instructions
  ; program-counter = Fin-zero-init
  ; tick            = 0
  } 

getInstr : (C : ControlUnit) → Instr (program-length C)
getInstr cu = lookup (program cu) (program-counter cu)


latch-program-counter : (C : ControlUnit) → Bool → ControlUnit
latch-program-counter cu true = record cu {program-counter = word-inc (program-counter cu)}
latch-program-counter cu false with getInstr cu
... | _ , _ , (jmp index) = record cu {program-counter = index}
... | _ , _ , (jz index)  = record cu {program-counter = index}
... | _ , _ , _           = cu

do-tick : ControlUnit → ControlUnit
do-tick cu = record cu {tick = current-tick cu + 1}

data Code : Set where
  RESULT PASS EXIT : Code

executeStep : ControlUnit → DataPath → IO (ControlUnit × DataPath × Code)
executeStep cu dp with pure (Instr.opcode (getInstr cu))
... | op = do
  HLT ← op
    where LEFT  → handle-address-shift LEFT {refl}
          RIGHT → handle-address-shift RIGHT {refl}
          PRINT → handle-printing
          INPUT → handle-memory-writing INPUT {refl}
          DEC   → handle-memory-writing DEC {refl}
          INC   → handle-memory-writing INC {refl}
          JZ    → handle-jz
          JMP   → pure $ do-tick (latch-program-counter cu false) |> (_,′ dp ,′ PASS) 
  pure (cu ,′ dp ,′ RESULT)

  where
    handle-address-shift : (op : Opcode) → {type op ≡ ADDRESS-SHIFT} → IO (ControlUnit × DataPath × Code)
    handle-address-shift op {proof} = let new-dp = latch-data-addr op {proof} dp
                                          new-cu = do-tick (latch-program-counter cu true)
                                      in pure (new-cu ,′ new-dp ,′ PASS)
                                      
    handle-memory-writing : (op : Opcode) → {type op ≡ MEMORY-WRITING} → IO (ControlUnit × DataPath × Code)
    handle-memory-writing op {proof} = let latched-dp = latch-acc dp
                                           first-tick = do-tick cu
                                           new-cu = do-tick (latch-program-counter first-tick true)
                                       in signal-wr op {proof} latched-dp >>=
                                       λ { (just new-dp) → pure (new-cu ,′ new-dp ,′ PASS)
                                         ; nothing       → pure (cu ,′ dp ,′ EXIT)
                                         }

    handle-printing : IO (ControlUnit × DataPath × Code)
    handle-printing =  let latched-dp = latch-acc dp
                           first-tick = do-tick cu
                           new-cu     = do-tick (latch-program-counter first-tick true)
                       in signal-output latched-dp >>=
                       λ new-dp → pure (new-cu ,′ new-dp ,′ PASS)
                       
    handle-jz : IO (ControlUnit × DataPath × Code)
    handle-jz = let latched-dp  = latch-acc dp
                    first-tick  = do-tick cu
                    should-jump = (not $ zero-flag latched-dp)
                    new-cu = do-tick (latch-program-counter first-tick should-jump)
                in pure (new-cu ,′ latched-dp ,′ PASS)



showControlUnit : ControlUnit → DataPath → String
showControlUnit cu dp = unwords
  $ ("TICK:  ")
  ∷ (ℕ.show (current-tick cu))
  ∷ " PC:   "
  ∷ (Fin.show (program-counter cu))
  ∷ " ADDR:   "
  ∷ (Fin.show (data-address dp))
  ∷ " MEM_OUT: "
  ∷ (Fin.show (readMemory dp))
  ∷ " ACC: "
  ∷ (Fin.show (acc dp))
  ∷ " 	"
  ∷ (showInstruction (getInstr cu)) ∷ []



runsteps : ℕ → ControlUnit → DataPath → IO {0ℓ} _
runsteps 0 cu dp = pure _
runsteps (suc n) cu dp = do
  result ← executeStep cu dp
  let new-cu = fst result
      new-dp = fst (snd result)
      code   = snd (snd result)

  when (not (isFinal code)) (debug (showControlUnit new-cu new-dp))
  when (n ≡ᵇ 1) (warning "Limit exceeded!")
  
  if (n ≡ᵇ 1) ∨ (isFinal code)
    then info ("output-buffer '" ++ (fromList (output-buffer new-dp)) ++ "'")
    else runsteps n new-cu new-dp

  where

    isFinal : Code → Bool
    isFinal RESULT = true
    isFinal EXIT   = true
    isFinal PASS   = false

runall : String → String → IO {0ℓ} _
runall code-content input-content = do
  let input-list = List.map charToWord (toList input-content)

  (just code) ← pure (parseJSON code-content)
    where nothing → die "Failed to parse instructions"

  (yes proof) ← pure ((length code) >? 0)
    where (no _) → die "Invalid program"

  let cp = controlunitInit {{>-nonZero proof}} code
      dp = datapathInit 100 (vecFromList input-list)
  
  runsteps 1200 cp dp


