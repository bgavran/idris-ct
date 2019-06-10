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
> data ConcatenationOfMorphisms : (cat : Category) -> (origin, target : obj cat) -> Type where
>   MkSingleMorphism    : mor cat a b -> ConcatenationOfMorphisms cat a b
>   MkCompositeMorphism : ConcatenationOfMorphisms cat a b
>                      -> ConcatenationOfMorphisms cat b c
>                      -> ConcatenationOfMorphisms cat a c
>
> composeConcatenationOfMorphisms : ConcatenationOfMorphisms cat a b -> mor cat a b
> composeConcatenationOfMorphisms (MkSingleMorphism f)                        = f
> composeConcatenationOfMorphisms (MkCompositeMorphism {cat} {a} {b} {c} f g) =
>   compose cat a b c (composeConcatenationOfMorphisms f) (composeConcatenationOfMorphisms g)
>
> record CommutativeDiagram (cat : Category) (origin : obj cat) (target : obj cat) where
>   constructor MkCommutativeDiagram
>   first    : ConcatenationOfMorphisms cat origin target
>   second   : ConcatenationOfMorphisms cat origin target
>   equality : composeConcatenationOfMorphisms first = composeConcatenationOfMorphisms second
>
> cdReflexivity : ConcatenationOfMorphisms cat a b -> CommutativeDiagram cat a b
> cdReflexivity mor = MkCommutativeDiagram mor mor Refl
>
> cdSymmetry : CommutativeDiagram cat a b -> CommutativeDiagram cat a b
> cdSymmetry (MkCommutativeDiagram first second equality) = MkCommutativeDiagram second first (sym equality)
>
> cdTransitivity :
>      (cd1, cd2 : CommutativeDiagram cat a b)
>   -> second cd1 = first cd2
>   -> CommutativeDiagram cat a b
> cdTransitivity (MkCommutativeDiagram first common equality1) (MkCommutativeDiagram common second equality2) Refl =
>   MkCommutativeDiagram first second (trans equality1 equality2)
