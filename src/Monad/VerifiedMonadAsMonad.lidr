attach\iffalse
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `idris-ct` Category Theory in Idris library.

Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
\fi

> module Monad.VerifiedMonadAsMonad
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalTransformation
> import Cats.CatsAsCategory
> import Cats.FunctorsAsCategory
> import Idris.FunctorAsCFunctor
> import Idris.TypesAsCategoryExtensional
> import Monad.Monad as M
>
> -- contrib
> import Interfaces.Verified
>
> %access public export
> %default total

interface Functor f => VerifiedFunctor (f : Type -> Type) where
  functorIdentity : {a : Type} -> (g : a -> a) -> ((v : a) -> g v = v) -> (x : f a) -> map g x = x
  functorComposition : {a : Type} -> {b : Type} -> (x : f a) ->
                       (g1 : a -> b) -> (g2 : b -> c) ->
                       map (g2 . g1) x = (map g2 . map g1) x

interface (Applicative f, VerifiedFunctor f) => VerifiedApplicative (f : Type -> Type) where
  applicativeMap : (x : f a) -> (g : a -> b) ->
                   map g x = pure g <*> x
  applicativeIdentity : (x : f a) -> pure Basics.id <*> x = x
  applicativeComposition : (x : f a) -> (g1 : f (a -> b)) -> (g2 : f (b -> c)) ->
                           ((pure (.) <*> g2) <*> g1) <*> x = g2 <*> (g1 <*> x)
  applicativeHomomorphism : (x : a) -> (g : a -> b) ->
                            (<*>) {f} (pure g) (pure x) = pure {f} (g x)
  applicativeInterchange : (x : a) -> (g : f (a -> b)) ->
                           g <*> pure x = pure (\g' : (a -> b) => g' x) <*> g

interface (Monad m, VerifiedApplicative m) => VerifiedMonad (m : Type -> Type) where
  monadApplicative : (mf : m (a -> b)) -> (mx : m a) ->
                     mf <*> mx = mf >>= \f =>
                                 mx >>= \x =>
                                        pure (f x)
  monadLeftIdentity : (x : a) -> (f : a -> m b) -> pure x >>= f = f x
  monadRightIdentity : (mx : m a) -> mx >>= Applicative.pure = mx
  monadAssociativity : (mx : m a) -> (f : a -> m b) -> (g : b -> m c) ->
                       (mx >>= f) >>= g = mx >>= (\x => f x >>= g)

>
> verifiedMonadToFunctor : VerifiedMonad m => Functor m
> verifiedMonadToFunctor @{monad} = %implementation
>
> verifiedMonadToVerifiedFunctor : VerifiedMonad m => VerifiedFunctor m
> verifiedMonadToVerifiedFunctor @{monad} = %implementation
>
> verifiedMonadToApplicative : VerifiedMonad m => Applicative m
> verifiedMonadToApplicative @{monad} = %implementation
>
> verifiedMonadToVerifiedApplicative : VerifiedMonad m => VerifiedApplicative m
> verifiedMonadToVerifiedApplicative @{monad} = %implementation
>
> verifiedMonadToMonad : VerifiedMonad m => Monad m
> verifiedMonadToMonad @{monad} = %implementation
>
> verifiedMonadToCFunctor : VerifiedMonad m => CFunctor TypesAsCategoryExtensional.typesAsCategoryExtensional
>                                                       TypesAsCategoryExtensional.typesAsCategoryExtensional
> verifiedMonadToCFunctor @{monad} = functorToCFunctor $ verifiedMonadToVerifiedFunctor @{monad}
>
> verifiedMonadMapPure :
>      (monad : VerifiedMonad m)
>   -> (g : a -> b)
>   -> (x : a)
>   -> map {f = m} g (pure x) = pure (g x)
> verifiedMonadMapPure monad g x = trans (applicativeMap @{verifiedMonadToVerifiedApplicative @{monad}} (pure x) g)
>                                        (applicativeHomomorphism @{verifiedMonadToVerifiedApplicative @{monad}} x g)
>
> verifiedMonadUnit :
>      (monad : VerifiedMonad m)
>   -> NaturalTransformation _ _ (idFunctor _) (verifiedMonadToCFunctor {m})
> verifiedMonadUnit {m} monad = MkNaturalTransformation
>   (\_ => MkExtensionalTypeMorphism $ pure)
>   (\a, b, f => case f of
>                  MkExtensionalTypeMorphism g => funExt $ verifiedMonadMapPure monad g)
>
> verifiedMonadMultiplicationComp :
>      (monad : VerifiedMonad m)
>   -> (a : Type)
>   -> mor TypesAsCategoryExtensional.typesAsCategoryExtensional
>          (mapObj (verifiedMonadToCFunctor @{monad}) (mapObj (verifiedMonadToCFunctor @{monad}) a))
>          (mapObj (verifiedMonadToCFunctor @{monad}) a)
> verifiedMonadMultiplicationComp monad a = MkExtensionalTypeMorphism $ join
>
> verifiedMonadMapJoin :
>      (monad : VerifiedMonad m)
>   -> (g : a -> b)
>   -> (x : mapObj (verifiedMonadToCFunctor @{monad}) (mapObj (verifiedMonadToCFunctor @{monad}) a))
>   -> map {f = m} g (join x) = join (map {f = m} (map {f = m} g) x)
>
> verifiedMonadMultiplication :
>      {m : Type -> Type}
>   -> (monad : VerifiedMonad m)
>   -> NaturalTransformation _ _ (functorComposition _ _ _ (verifiedMonadToCFunctor @{monad})
>                                                          (verifiedMonadToCFunctor @{monad}))
>                                (verifiedMonadToCFunctor @{monad})
> verifiedMonadMultiplication monad = ?asdf

-- > verifiedMonadMultiplication {m} monad = MkNaturalTransformation
-- >   (verifiedMonadMultiplicationComp monad)
-- >   ?asdf

-- >   (\a, b, f => case f of
-- >                  MkExtensionalTypeMorphism g => funExt $ verifiedMonadMapJoin monad g)

-- >
-- > verifiedMonadAssociativity :
-- >      (monad : VerifiedMonad m)
-- >   -> MonadAssociativity (verifiedMonadToCFunctor @{monad}) (verifiedMonadMultiplication monad)
-- >
-- > verifiedMonadLeftUnit :
-- >      (monad : VerifiedMonad m)
-- >   -> MonadLeftUnit (verifiedMonadToCFunctor @{monad}) (verifiedMonadUnit monad) (verifiedMonadMultiplication monad)
-- >
-- > verifiedMonadRightUnit :
-- >      (monad : VerifiedMonad m)
-- >   -> MonadRightUnit (verifiedMonadToCFunctor @{monad}) (verifiedMonadUnit monad) (verifiedMonadMultiplication monad)
-- >
-- > verifiedMonadToMonad :
-- >      VerifiedMonad m
-- >   -> M.Monad TypesAsCategoryExtensional.typesAsCategoryExtensional
-- > verifiedMonadToMonad {m} monad = MkMonad
-- >   (functorToCFunctor $ verifiedMonadToVerifiedFunctor @{monad})
-- >   (verifiedMonadUnit @{monad})
-- >   (verifiedMonadMultiplication @{monad})
-- >   (verifiedMonadAssociativity @{monad})
-- >   (verifiedMonadLeftUnit @{monad})
-- >   (verifiedMonadRightUnit @{monad})
