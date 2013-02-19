{-# LANGUAGE OverloadedStrings, FlexibleInstances, GADTs #-}
module Main where

import Data.Monoid
import Data.String
import Gentzen.Term
import Gentzen.Metalogic
import Gentzen.Display
import Gentzen.Rule
import Gentzen.TypeEnv
import Gentzen.Typechecker
import Gentzen.Vector as V
import Gentzen.FreeSubst as F
import Gentzen.TypeLevel
import Gentzen.Equation
import Gentzen.Unification
import System.Console.ANSI
import System.Console.Haskeline
import Data.List (isPrefixOf)
import Control.Monad.Trans
import Gentzen.RuleEnv
import Control.Arrow
import Control.Monad(forM, when)

instance IsString (Maybe String) where
  fromString = Just

logo = unlines ["                                      "
               ,"▐█▓▒░ ┌───┐┌──┌─┐ ─┬───┐┌──┌─┐        "
               ,"▐█▓▒░ │   ┐├─ │ │  │ ┌─┘├─ │ │        "
               ,"▐█▓▒░ └───┘└──┴ └┘ ┴ └──└──┴ └┘       "
               ,"▐█▓▒░ ═════════════════════════════   "
               ,"▐█▓▒░                                 "
               ,"▐█▓▒░ Version 0.01                    "
               ,"                                      "
               ]

main = do setSGR [SetColor Foreground Vivid Yellow]
          putStrLn logo
          setSGR [Reset]
          runInputT defaultSettings $ main' show show (Q (startΓ) (startΔ) [] EmptyC :> test0) True

main' :: (Show a, Eq a) => (a -> String) -> (r -> String) ->  Q a r -> Bool -> InputT IO ()
main' te re (Q _ _ _ EmptyC :< (π , ρ)) d = do
   liftIO $ setSGR [SetColor Foreground Vivid Yellow]
   outputStrLn $ "Proved: " ++ ppr (displayRule te ρ)
   liftIO $ setSGR [Reset]
main' te re st@(Q _ _ _ _ :< _) d = do liftIO $ setSGR [SetColor Foreground Vivid Black]
                                       outputStrLn $ displayState te re st
                                       let Right st' = next st
                                       main' te re st' True
main' te re st d = do when d $ do liftIO $ setSGR [SetColor Foreground Vivid White]
                                  outputStrLn $ displayState te re st
                      liftIO $ setSGR [SetColor Foreground Vivid Green]
                      c <- getInputLine "gentzen> "
                      liftIO $ setSGR [Reset]
                      case c of Just "next" -> action next
                                Just "back" -> action back
                                Just "rules" -> printRules te st >> main' te re st False
                                Just "exit" -> liftIO $ setSGR [Reset]
                                Just str | "apply" `isPrefixOf` str -> do
                                       x <- case words (drop 5 str) of
                                              [a,b] -> apply a (read b) te re st
                                              [a]   -> apply a 100      te re st
                                              _      -> return Nothing
                                       case x of Nothing -> main' te re st True
                                                 Just st' -> main' te re st' True
                                Just "unprove" -> action unprove
                                Just "clear" -> main' show show (Q (startΓ) (startΔ) [] EmptyC :> test0) True
                                Just "example 1" -> main' show show (Q (startΓ) (startΔ) [] EmptyC :> test1) True
                                Just "example 2" -> main' show show (Q (startΓ) (startΔ) [] EmptyC :> test2) True
                                _ -> main' te re st True
  where action act = case act st of
                      Right st' -> main' te re st' True
                      Left str  -> do liftIO $ setSGR [SetColor Foreground Vivid Red] 
                                      outputStrLn str
                                      liftIO $ setSGR [Reset]
                                      main' te re st False
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


apply :: (Show a, Eq a) => String -> Int -> (a -> String) -> (r -> String) -> Q a r -> InputT IO (Maybe (Q a r))
apply rule depth te re st@(Q γ δ ξ φ :> Show (Unproven (Holds Nil [] e)))
  | Just ρ <- fmap (Gentzen.RuleEnv.lookup δ) $ lookupString δ rule
  = do outputStrLn $ "Applying rule " ++ rule ++ " (depth " ++ show depth ++ ") to goal:"
       outputStrLn $ ppr $ displayTerm te' e
       case enfreshinate ρ
        of (Holds Nil ρs e', locals) -> do
             let Right eq = runTCM $ typecheckEq γ (e :=: e')
             let ξ' = fmap (λ' $ contextVars φ) eq:ξ
             let v = flip runUnificationM 3 $ unify depth (γ . upN (V.length $ contextVars φ)) ξ'
             case v of
               Left err -> return Nothing
               Right (sols,int) -> do
                 liftIO $ print $ map (ppr . displaySolution te . fst) sols
                 return $ Just st
  | otherwise = do outputStrLn $ "Rule " ++ rule ++ " not found."
                   return $ Just st
  where te' = contextVars φ `V.expandDomainN` te

printRules :: (a -> String) -> Q a r -> InputT IO ()
printRules te (Q _ (Δ δ m) _ φ :> _) =
   let te' = contextVars φ `V.expandDomainN` te
       ls = map (second $ ppr . displayRule te' . δ) m
    in flip mapM_ ls $ \(name, rule) -> do liftIO $ setSGR [SetColor Foreground Vivid Blue]
                                           outputStrLn name
                                           liftIO $ setSGR [Reset]
                                           outputStrLn rule

data BuiltIns = And
              | Imp
              | TrueP
              deriving (Eq, Show)

data BuiltInRules = AndI
                  | ImpI
                  | TrueI deriving Show

startΓ :: Γ BuiltIns
startΓ And = "Prop" → "Prop" → "Prop"
startΓ Imp = "Prop" → "Prop" → "Prop"
startΓ TrueP = "Prop"

startΔ :: Δ BuiltInRules BuiltIns
startΔ = Δ startρ' lookupTable
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
        startρ' TrueI = Holds Nil [] (Λ Nil (RV $ TrueP) [])
        lookupTable = [("AndI",AndI),("ImpI", ImpI), ("TrueI",TrueI)]

test0 :: ProofStatement BuiltIns BuiltInRules
test0 = Show $ ProvenBy (rtε' (RV $ TrueP)) (TrueI, mempty)

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
               $ Show $ Inline (andF [tε a, andF [tε b, tε c]]) (andI,F.fromList [(("?P","Prop"), tε a), (("?Q","Prop"), andF [tε b, tε c])])
                          [ProvenBy (rtε' a) (aTrue, mempty)
                          ,Inline (andF [tε b, tε c]) (andI, F.fromList [(("?P","Prop"), tε b)
                                                                        ,(("?Q","Prop"), tε c)] )
                             [ProvenBy (rtε' b) (bTrue, mempty)
                             ,ProvenBy (rtε' c) (cTrue, mempty)
                             ]
                          ]

test2 :: ProofStatement BuiltIns BuiltInRules
test2 = ForAll "P" "Prop" $ ForAll "Q" "Prop"
          $ Lemma "ℓ " ell
          $ Show $ let impI = suc ImpI
                    in Inline (impF [tε p, impF [tε q, andF[tε p, tε q]]])
                             (impI, F.fromList [(("?P", "Prop"), tε p)
                                               ,(("?Q", "Prop"), impF [tε q, andF [tε p, tε q]])])
                             [ProvenBy (Holds' Nil [rtε p] (impF [tε q, andF [tε p, tε q]])) (zero, mempty)]
  where ell = Assuming "a1" (rtε p) $ Lemma "ℓ₁" ell1 $ Show $ let impI = suc $ suc ImpI
                 in Inline (impF [tε q, andF[tε p, tε q]]) (impI, F.fromList [(("?P","Prop"), tε q), (("?Q","Prop"), andF [tε p, tε q])])
                           [ProvenBy (Holds' Nil [rtε q] (andF [tε p, tε q])) (zero, mempty)]
        ell1 = Assuming "a2" (rtε q) $ Show $ Inline (andF [tε p, tε q]) (suc $ suc AndI, F.fromList [(("?P","Prop"), tε p),(("?Q", "Prop"), tε q)])
                  [ProvenBy (rtε' p) (suc zero, mempty), ProvenBy (rtε' q) (zero, mempty)]
        imp = RV $ suc $ suc Imp
        and = RV $ suc $ suc And
        andF = Λ Nil and
        impF = Λ Nil imp
        p = RV $ suc zero
        q = RV $ zero

