{- Copyright (C) 2015 Jake Ehrlich and Graham Leach-Krouse <gleachkr@ksu.edu>

This file is part of Carnap 

Carnap is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Carnap is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with Carnap. If not, see <http://www.gnu.org/licenses/>.
- -}

module Carnap.Languages.Util.ParserTypes where
import Text.Parsec

--------------------------------------------------------
--1. Parser Packages
--------------------------------------------------------
--In principle, different parsers can maintain different sorts of state.
--However, since we want to be able to change the settings of our parsers,
--and pass variously set parsers to the same functions, and espcially use
--one parser inside another, in practice we can avoid headaches by making
--them all formula parsers carry the same kind of state.

data FParser f st = FParser { parser :: Parsec String st f, initState :: st }

stateParse :: FParser f st -> String -> Either ParseError f
stateParse p = runParser (parser p) (initState p) ""

--------------------------------------------------------
--2. User State
--------------------------------------------------------

--This is a data type for the user state maintained by a given
--parser. It includes configuration information, and
--other features of the parser. 

data UserState = UserState { strict :: Bool }
