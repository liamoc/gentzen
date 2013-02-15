{-# LANGUAGE GeneralizedNewtypeDeriving, GADTs, ImplicitParams #-}
module Gentzen.ProofChecker where
import Gentzen.Term
import Gentzen.Rule
import Gentzen.Metalogic
import Gentzen.TypeEnv
import qualified Gentzen.Vector as V
import Gentzen.Vector(Vec(..))
import Gentzen.TypeLevel
import Gentzen.Typechecker
import Gentzen.Equation
import Gentzen.Unification

import Control.Applicative
import Control.Monad.Error hiding (mapM,sequence)
import Data.Foldable
import Data.Traversable

import Prelude hiding (mapM, sequence, concat)

data ProofError = PE String | TE TypeError

instance Error ProofError where
  strMsg = PE

newtype ProofCheckM a = PCM (Either ProofError a)
                      deriving (Monad, Applicative, Functor, MonadError ProofError)

check' :: Eq a => Γ a -> (r -> Rule a) -> ProofStatement a r -> ProofCheckM (ProofStatement a r)
check' env rules (ForAll s τ st)
   = fmap (ForAll s τ) $ check' (env `extend` τ) (fmap suc . rules) st
check' env rules (Assuming n r st) = fmap (Assuming n r) $ check' env (V.expandDomain (Cons n r Nil) rules) st
check' env rules (Lemma n r st)    = do r' <- check' env rules r
                                        fmap (Lemma n r') $ check' env (V.expandDomain (Cons n (rule r') Nil) rules) st
check' env rules (Show tr) = fmap Show $ checkTree env rules tr

tcmToProofCheckM :: TCM a -> ProofCheckM a
tcmToProofCheckM = either (throwError . TE) return . runTCM

checkTree :: Eq a => Γ a -> (r -> Rule a) -> ProofTree a r -> ProofCheckM (ProofTree a r)
checkTree env rules it@(Inline t (r, (subst, rem)) ch) | r' <- rules r
   = let rule₁ = subst `freeSubstRule` enfreshinate r'
         rule₂ = ruleTree it
      in case ruleEquations rule₁ rule₂ of
            Just eqs -> do eqs' <- mapM (tcmToProofCheckM . typecheckEq env) eqs
                           if checkSolution eqs' rem
                             then Inline t (r, (subst, rem)) <$> mapM (checkTree env rules) ch
                             else throwError $ PE "Solution is not valid"
            Nothing  -> throwError $ PE "Rules have differing numbers of premises."
  where ruleEquations :: (Rule x) -> (Rule x) -> Maybe [Equation (Term Raw x)]
        ruleEquations (Holds τs₁ ρs₁ c₁) (Holds τs₂ ρs₂ c₂)
           | Just Refl <- V.eq τs₁ τs₂
           = do guard (length ρs₁ == length ρs₂)
                rest <- concat <$> sequence (zipWith ruleEquations ρs₁ ρs₂)
                return $ map (fmap (λ' τs₁)) $ (c₁ :=: c₂) : rest
           | otherwise = Nothing
