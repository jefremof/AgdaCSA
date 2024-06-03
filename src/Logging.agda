{-# OPTIONS --guardedness #-}

module Logging where

open import Agda.Builtin.Unit
open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List ; _∷_ ; [])
open import Data.Maybe.Base using (Maybe; just; nothing ; fromMaybe)
open import Data.Nat.Base using (ℕ ; _≤ᵇ_)
open import Data.String.Base using (String ; _++_)

open import Function.Base using (id; _$_; case_of_ ; _∘_)
open import IO
open import Level
open import System.Environment using (lookupEnv)

data LogLevel : Set where
  DEBUG INFO WARNING : LogLevel

levelToNat : LogLevel → ℕ
levelToNat DEBUG    = 0
levelToNat INFO     = 1
levelToNat WARNING  = 2

infix 4 _≥ᵇ_

_≥ᵇ_ : LogLevel → LogLevel → Bool
a ≥ᵇ b = (levelToNat b) ≤ᵇ (levelToNat a)

parseLevel : String → LogLevel
parseLevel "DEBUG"    = DEBUG
parseLevel "INFO"     = INFO
parseLevel "WARNING"  = WARNING
parseLevel default    = DEBUG

showLevel : LogLevel → String
showLevel DEBUG    = "DEBUG"
showLevel INFO     = "INFO"
showLevel WARNING  = "WARNING"

lookupLevel : IO LogLevel
lookupLevel = parseLevel ∘ (fromMaybe "nothing") <$> lookupEnv "AgdaLogLevel"

log : LogLevel → String → IO {0ℓ} _
log loglevel message = (loglevel ≥ᵇ_ <$> lookupLevel) >>= λ x → (when x (putStrLn message))

debug : String → IO {0ℓ} _
debug msg = log DEBUG ("DEBUG   " ++ msg)

info : String → IO {0ℓ} _
info msg = log INFO ("INFO   " ++ msg)

warning : String → IO {0ℓ} _
warning msg = log WARNING ("WARNING   " ++ msg)
