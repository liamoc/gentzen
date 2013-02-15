{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving #-}
module Gentzen.Typechecker where

import Gentzen.TypeLevel
import Gentzen.Term
import Gentzen.TypeEnv
import Gentzen.Equation
import qualified Gentzen.Vector as V
import Gentzen.Vector (Vec (..))
import Control.Monad.Error hiding (mapM, forM, sequence)
import Prelude hiding (lookup)
import Control.Applicative

data TypeError = TypeMismatch Type Type
               | ShouldBeFunction Type
               | UnknownAtom String
               | OtherError String
               deriving Show

instance Error TypeError where
  strMsg = OtherError

newtype TCM a = TCM { runTCM :: Either TypeError a }
              deriving (Monad, Functor, Applicative, Alternative, MonadPlus, MonadError TypeError)

assertEqual :: Type -> Type -> TCM ()
assertEqual τ₁ τ₂ = when (τ₁ /= τ₂) $ throwError $ TypeMismatch τ₁ τ₂

ηlnf :: Γ a -> Term Raw a -> TCM (Term Typechecked a, Type)
ηlnf envΓ (Λ (Cons n τ₁ τs) h ts) = do (e', τ₂) <- ηlnf (envΓ `extend` τ₁) (Λ τs h ts)
                                       return (λ (n, τ₁) e', τ₁ → τ₂)
ηlnf envΓ (Λ Nil h ts) = do let τ₀      = lookup envΓ h
                                (τs, τ) = splitType τ₀
                            case compare (length ts) (length τs) of
                              GT -> throwError $ ShouldBeFunction τ
                              EQ -> do (ts', τs') <- unzip <$> mapM (ηlnf envΓ) ts
                                       zipWithM_ assertEqual τs τs'
                                       return (Λ Nil (toTC h τ₀) ts', τ)
                              LT -> let ρ:_ = drop (length ts) τs
                                     in ηlnf envΓ $ Λ (Cons Nothing ρ Nil)
                                                      (fmap suc h)
                                                      (map (fmap suc) ts ++ [return zero])
   where toTC :: Raw a -> Type -> Typechecked a
         toTC (RV ν) = V ν
         toTC (RA c τ) = const $ A c τ

typecheck = ηlnf

typecheckEq :: Γ a -> Equation (Term Raw a) -> TCM (Equation (Term Typechecked a))
typecheckEq envΓ (t₁ :=: t₂) = do (t₁', τ₁) <- ηlnf envΓ t₁
                                  (t₂', τ₂) <- ηlnf envΓ t₂
                                  assertEqual τ₁ τ₂
                                  return $ t₁' :=: t₂'
