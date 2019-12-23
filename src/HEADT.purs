module HEADT where

import Prelude

import Data.Lens (Iso, Prism', iso, prism')
import Data.Maybe (Maybe)
import Data.Newtype (unwrap, wrap)
import Data.Symbol (class IsSymbol, SProxy)
import HFunctor.Variant (HProxy, HVariantF)
import HFunctor.Variant as HVF
import Higher (class HFunctor, HAlgebra, HMu(..), HCoalgebraM)
import Prim.Row as R

type HEADT t = HMu (HVariantF t)

_HMu :: forall f h. Iso (h (HMu h) f) (h (HMu h) f) (HMu h f) (HMu h f)
_HMu = iso HMu (\(HMu m) -> m)

inj
  ∷ forall h s a b
  . R.Cons s (HProxy h) a b 
  => IsSymbol s 
  => HFunctor h 
  => SProxy s 
  -> HAlgebra h (HEADT b)
inj label = wrap <<< HVF.inj label

prj
  :: forall h s a b
  . R.Cons s (HProxy h) a b 
  => IsSymbol s
  => HFunctor h
  => SProxy s 
  -> HCoalgebraM Maybe h (HEADT b)
prj label = HVF.prj label <<< unwrap

_HVariantF
  :: forall l h f v a
   . IsSymbol l
  => HFunctor h
  => R.Cons l (HProxy h) _ v
  => SProxy l
  -> Prism' (HVariantF v f a) (h f a)
_HVariantF label = prism' (HVF.inj label) (HVF.prj label)

_HEADT 
  :: forall l h f a
   . IsSymbol l 
   => HFunctor h 
   => R.Cons l (HProxy h) _ f
   => SProxy l 
   -> Prism' (HEADT f a) (h (HEADT f) a)
_HEADT label = prism' (inj label) (prj label) 