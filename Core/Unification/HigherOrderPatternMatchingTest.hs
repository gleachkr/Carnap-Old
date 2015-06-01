import Carnap.Core.Unification.HigherOrderPatternMatching
import Carnap.Core.Unification.HigherOrderUtilLens

--the type of terms in our langauge
data Term = Constant String
          | Function String Term

data Schema = Schematic String
            | SConnective String [Schema]
            | SPredicate String [Term]

data Concrete = Connective String [Concrete]
              | Predicate String [Term]