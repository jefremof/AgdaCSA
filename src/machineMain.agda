{-# OPTIONS --guardedness #-}

open import Data.List using (List ; [] ; _∷_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.String.Base using (String ; unlines ; unwords ; _++_)
open import Function.Base using (_∘_ ; _$_)
open import IO
open import Logging
open import System.Environment using (getArgs ; setEnv ; unsetEnv)
open import System.Exit using (exitSuccess ; die)

open import machineInner using (runall)

module machineMain where


record Options : Set where
  constructor _,_,_
  field
    code-file  : String
    input-file : String
    log-level  : LogLevel
open Options


initOptions : String → String → LogLevel → Options
initOptions codefile inputfile loglvl = record
  { code-file  = codefile
  ; input-file = inputfile
  ; log-level  = loglvl
  }

usage : String
usage = unwords
  $ "Usage:"
  ∷ "machine <code-file> <input-file>"
  ∷ "[log-level]"
  ∷ []

options : List String → IO (Maybe Options)
options (x ∷ y ∷ [])     = pure $ just (initOptions x y DEBUG)
options (x ∷ y ∷ z ∷ []) = pure $ just (initOptions x y (parseLevel z))
{-# CATCHALL #-}
options _                = pure nothing


main : Main
main = run $ do
  args ← getArgs
  just (codefile , inputfile , loglevel) ← options args
    where nothing → die (unlines ("Wrong arguments" ∷ usage ∷ []))

  code-content  ← readFiniteFile codefile
  input-content ← readFiniteFile inputfile
  setEnv "AgdaLogLevel" (showLevel loglevel)

  runall code-content input-content

  unsetEnv "AgdaLogLevel"
  exitSuccess
