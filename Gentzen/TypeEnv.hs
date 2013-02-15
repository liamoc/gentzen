module Gentzen.TypeEnv where

import Gentzen.Term
import Gentzen.TypeLevel

type Γ a = (a -> Type)

extend :: Γ a -> Type -> Γ (Suc a)
extend = flip maybe

lookup :: Γ a -> Raw a -> Type
lookup vΓ (RV ν) = vΓ ν
lookup vΓ (RA c τ) = τ
