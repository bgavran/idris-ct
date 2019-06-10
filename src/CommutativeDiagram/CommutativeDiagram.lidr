\iffalse
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

> module CommutativeDiagram.CommutativeDiagram
>
> import Basic.Category
>
> %access public export
> %default total
>
> record CommutativeSquare (cat : Category) (source : obj cat) (target : obj cat) where
>   constructor MkCommutativeSquare
>   a : obj cat
>   b : obj cat
>   f : mor cat source a
>   g : mor cat a target
>   h : mor cat source b
>   i : mor cat b target
>   equality : compose cat source a target f g = compose cat source b target h i
>
> csReflexivity : (f : mor cat source a) -> (g : mor cat a target) -> CommutativeSquare cat source target
> csReflexivity {a} f g = MkCommutativeSquare a a f g f g Refl
>
> csSymmetry : CommutativeSquare cat source target -> CommutativeSquare cat source target
> csSymmetry (MkCommutativeSquare a b f g h i equality) = MkCommutativeSquare b a h i f g (sym equality)
>
> transitivityLemma :
>      (h1 : mor cat source b1)
>   -> (i1 : mor cat b1 target)
>   -> (f2 : mor cat source a2)
>   -> (g2 : mor cat a2 target)
>   -> (h2 : mor cat source b2)
>   -> (i2 : mor cat b2 target)
>   -> (b1Ea2 : b1 = a2)
>   -> (h1Ef2 : h1 = f2)
>   -> (i1Ef2 : i1 = g2)
>   -> (equality : compose cat source a2 target f2 g2 = compose cat source b2 target h2 i2)
>   -> compose cat source b1 target h1 i1 = compose cat source b2 target h2 i2
> transitivityLemma f2 g2 f2 g2 h2 i2 Refl Refl Refl equality = equality
>
> csTransitivity :
>      (cs1, cs2 : CommutativeSquare cat source target)
>   -> (b cs1 = a cs2)
>   -> (h cs1 = f cs2)
>   -> (i cs1 = g cs2)
>   -> CommutativeSquare cat source target
> csTransitivity (MkCommutativeSquare a1 b1 f1 g1 h1 i1 eq1)
>                (MkCommutativeSquare a2 b2 f2 g2 h2 i2 eq2)
>                b1Ea2 h1Ef2 i1Eg2 =
>   MkCommutativeSquare a1 b2 f1 g1 h2 i2 (trans eq1 (transitivityLemma h1 i1 f2 g2 h2 i2 b1Ea2 h1Ef2 i1Eg2 eq2))
