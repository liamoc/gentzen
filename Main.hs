{-# LANGUAGE OverloadedStrings, FlexibleInstances, GADTs #-}
module Main where

import Data.Monoid
import Data.String
import Gentzen.Term
import Gentzen.Metalogic
import Gentzen.Display
import Gentzen.Rule
import Gentzen.TypeEnv
import Gentzen.Vector
import Gentzen.FreeSubst as F
import Gentzen.TypeLevel
import Gentzen.RuleEnv

instance IsString (Maybe String) where
  fromString = Just

main = main' show show $ (Q (startΓ) (startΔ) [] EmptyC :> test1)

main' :: (Eq a) => (a -> String) -> (r -> String) ->  Q a r -> IO ()
main' te re (Q _ _ _ EmptyC :< (π , ρ)) = putStrLn $ "Proved: " ++ ppr (displayRule te ρ)
main' te re st = do putStrLn $ displayState te re st 
                    _ <- getChar 
                    main' te re (next st)

data Void

instance Eq Void where
  (==) = undefined

foo :: Void -> a
foo = undefined

rε = Holds Nil []
rε' = Holds' Nil []
tε = flip (Λ Nil) []
rtε = rε . tε
rtε' = rε' . tε



data BuiltIns = And
              | Imp
              deriving (Eq, Show)

data BuiltInRules = AndI
                  | ImpI deriving Show

startΓ :: Γ BuiltIns
startΓ And = "Prop" → "Prop" → "Prop"
startΓ Imp = "Prop" → "Prop" → "Prop"

startΔ :: Δ BuiltInRules BuiltIns
startΔ = Δ startρ'
  where startρ' AndI = (Holds (Cons "P" "Prop" $ Cons "Q" "Prop" Nil)
                          [ rtε $ RV $ suc zero
                          , rtε $ RV   zero      ]
                          (Λ Nil (RV $ suc $ suc And) [tε $ RV $ suc zero
                                                      ,tε $ RV $ zero
                                                      ]))
        startρ' ImpI = (Holds (Cons "P" "Prop" $ Cons "Q" "Prop" Nil)
                          [ Holds Nil [rtε $ RV $ suc zero] (tε $ RV $ zero) ]
                          (Λ Nil (RV $ suc $ suc Imp) [tε $ RV $ suc zero
                                                      ,tε $ RV $ zero
                                                      ]))


test1 :: ProofStatement BuiltIns BuiltInRules
test1 = ForAll "A" "Prop" $ ForAll "B" "Prop" $ ForAll "C" "Prop"
           $ let a = RV $ suc $ suc zero
                 b = RV $ suc zero
                 c = RV $ zero
                 and = RV $ suc $ suc $ suc $ And
                 andF = Λ Nil and 
                 andI = suc $ suc $ suc AndI
                 aTrue = suc $ suc zero
                 bTrue = suc zero
                 cTrue = zero
              in Assuming "A_true" (rtε a)
               $ Assuming "B_true" (rtε b)
               $ Assuming "C_true" (rtε c)
               $ Show $ Inline (andF [tε a, andF [tε b, tε c]]) (andI,F.fromList [(("?1","Prop"), tε a), (("?2","Prop"), andF [tε b, tε c])])
                          [ProvenBy (rtε' a) (aTrue, mempty)
                          ,Inline (andF [tε b, tε c]) (andI, F.fromList [(("?1","Prop"), tε b)
                                                                        ,(("?2","Prop"), tε c)] )
                             [ProvenBy (rtε' b) (bTrue, mempty)
                             ,ProvenBy (rtε' c) (cTrue, mempty)
                             ]
                          ]

