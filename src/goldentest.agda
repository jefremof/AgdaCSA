{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Sigma using (fst ; snd)
open import Agda.Builtin.Unit using (⊤)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
-- open import Data.Fin using (#_)
-- open import Data.Fin.Base as Fin using (Fin ; suc ; zero ; toℕ ; pred)
open import Data.List using (List ; [] ; _∷_ ; length)
open import Data.Nat.Base
open import Data.Nat.Show using (show)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.String.Base using (String ; unlines ; unwords ; _++_ ; lines ; _<+>_)
open import Data.String.Properties as String using (_==_)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; fromList)
open import Function.Base using (_∘_ ; _$_)
open import IO
open import Level using (0ℓ)
open import Logging
open import System.Environment using (getArgs ; setEnv ; unsetEnv)
open import System.Process using (readProcessWithExitCode)
open import System.Exit using (exitSuccess ; exitFailure ; isFailure ; die)

module goldentest where


record Options : Set where
  constructor _,_,_,_,_
  field
    testlist      : String
    translator : String
    machine    : String
    log-level  : LogLevel
    overwrite  : Bool
open Options


initOptions : String → String → String → LogLevel → String → Options
initOptions testpath translator machine loglvl overwr = record
  { testlist      = testpath
  ; translator = translator
  ; machine    = machine
  ; log-level  = loglvl
  ; overwrite  = if (overwr String.== "TRUE") then true else false
  }

usage : String
usage = unwords
  $ "Usage:"
  ∷ "goldentest <root> <translator> <machine>"
  ∷ "[log-level [overwrite]]"
  ∷ []

options : List String → IO (Maybe Options)
options (t ∷ x ∷ y ∷ [])     = pure $ just (initOptions t x y DEBUG "")
options (t ∷ x ∷ y ∷ z ∷ []) = pure $ just (initOptions t x y (parseLevel z) "")
options (t ∷ x ∷ y ∷ z ∷ w ∷ []) = pure $ just (initOptions t x y (parseLevel z) w)
{-# CATCHALL #-}
options _                = pure nothing

separator = "============================================================\n"


runtest : ℕ → String → Options → IO Bool
runtest n testname (testpath , translator , machine , loglevel , overwrite) = do
  let codesource     = testpath ++ testname ++ "\\source.txt"
      inputfile      = testpath ++ testname ++ "\\input.txt"
      expectedfile   = testpath ++ testname ++ "\\expected.txt"
      tempfile       = testpath ++ testname ++ "\\temp.txt"
      translatorargs = (codesource ∷ tempfile ∷ [])
      machineargs    = (tempfile ∷ inputfile ∷ (showLevel loglevel) ∷ [])

  result ← readProcessWithExitCode translator translatorargs ""
  let exitcode = fst result
      output   = fst (snd result)
      errlog   = snd (snd result)

  false ← pure (isFailure exitcode)
    where true → (onFailure "Translation failed" errlog) >> pure false

  result′ ← readProcessWithExitCode machine machineargs ""
  let exitcode′ = fst result′
      output′   = fst (snd result′)
      errlog′   = snd (snd result′)

  false ← pure (isFailure exitcode′)
    where true → (onFailure "Machine failed" errlog′) >> pure false

  expected-content ← readFiniteFile expectedfile
  let program-output = output ++ separator ++ output′

  putStrLn program-output
  putStrLn separator
  putStrLn expected-content
  putStrLn separator

  ignore (writeFile tempfile program-output)

  when overwrite (ignore (writeFile expectedfile program-output))

  if (program-output String.== expected-content)
    then (putStrLn ("Test " ++ (show n) <+> testname ++ "\nSUCCESS\n") >> pure true)
    else (putStrLn ("Test " ++ (show n) <+> testname ++ "\nFAILED\n") >> pure false)

  where
  onFailure : String → String → IO _
  onFailure causedBy errlog = putStrLn (unlines $ ("Test " ++ (show n)) ∷ causedBy ∷ errlog ∷ [])

    
runtests : Options → IO Bool
runtests opts = do
  expected-content ← readFiniteFile ((testlist opts)++"tests.txt")
  let tests = lines expected-content
      n = length tests

  countdown n (fromList tests) n 0 >>= pure ∘ (_≡ᵇ n)

  where
  countdown : ∀ (k) → Vec String k → ℕ → ℕ → IO ℕ
  countdown 0 [] n m    = putStrLn ("\n" ++ show m ++ " \\ " ++ show n ++ " Tests passed\n") >> pure m
  countdown (suc k) (x ∷ xs) n m = do
    result ← runtest (n ∸ k) x opts
    countdown k xs n (if result then (m + 1) else m)


main : Main
main = run $ do
  args ← getArgs
  just opts ← options args
    where nothing → die (unlines ("Wrong arguments" ∷ usage ∷ []))

  successful ← runtests opts
  if successful then exitSuccess else exitFailure
