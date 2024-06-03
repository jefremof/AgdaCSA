{-# OPTIONS --guardedness #-}

open import Data.List using (List ; [] ; _∷_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.String.Base using (String ; unlines ; unwords ; _++_)
open import Function.Base using (_∘_ ; _$_)
open import IO
open import Logging
open import System.Environment using (getArgs ; setEnv ; unsetEnv)
open import System.Exit using (exitSuccess ; die)

open import translatorInner

module translatorMain where


record Options : Set where
  constructor _,_,_
  field
    input-file  : String
    output-file : String
open Options


initOptions : String → String  → Options
initOptions inputfile outputfile = record
  { input-file  = inputfile
  ; output-file = outputfile
  }

usage : String
usage = unwords
  $ "Usage:"
  ∷ "translator <code-file> <input-file>"
  ∷ []


main : Main
main = run $ do
  inputfile ∷ outputfile ∷ [] ← getArgs
    where {-# CATCHALL #-} instead → die (unlines ("Wrong arguments" ∷ usage ∷ []))

  input-content ← readFiniteFile inputfile

  translate input-content outputfile

  exitSuccess
