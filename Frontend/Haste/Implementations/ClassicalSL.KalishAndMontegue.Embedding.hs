--{-# LANGUAGE  OverloadedStrings, DeriveDataTypeable #-} 
module Main where
import Carnap.Frontend.Haste.Components.ProofPadEmbedding
import Carnap.Calculi.ClassicalSententialLogic1 (classicalRules, classicalSLruleSet)

main = embedWith (classicalRules, classicalSLruleSet)
