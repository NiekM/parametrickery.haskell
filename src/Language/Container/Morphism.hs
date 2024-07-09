-- TODO: perhaps rename to Language.Container.Example?
--       although it is a bit confusing...
module Language.Container.Morphism where

import Control.Monad.Error.Class
import Data.List.NonEmpty qualified as NonEmpty
import Control.Arrow ((&&&))

import Base
import Data.Map.Multi (Multi)
import Data.Map.Multi qualified as Multi
import Data.Named
import Prettyprinter.Utils
import Utils

import Language.Type
import Language.Expr
import Language.Container
import Language.Container.Relation

-- TODO: maybe rewrite with some other datatype?
type Origins = Multi Position Position

computeOrigins :: Ord a => Map Position a -> Map Position a -> Origins
computeOrigins p q = Multi.remapping (Multi.fromMap q) (Multi.fromMap p)

-- A polymorphic input-output example, i.e. an input-output example for
-- container morphisms.
data PolyExample = PolyExample
  { relations :: [Relation]
  , inShapes  :: [Shape]
  , outShape  :: Shape
  , origins   :: Origins
  } deriving stock (Eq, Ord, Show)

-- It seems that we only need to compute the relation for the inputs, since the
-- output values are a subset (and if they are not, this is already a conflict).
checkExample :: Signature -> Example -> Result PolyExample
checkExample Signature { constraints, context, goal } Example { inputs, output }
  | conflict  = throwError PositionConflict
  | otherwise = return PolyExample { relations, inShapes, outShape, origins }
  where
    Container outShape q = toContainer goal output

    ins      = toContainers $ zip (value <$> context) inputs
    inShapes = shape <$> ins
    p        = foldMap positions ins

    relations = computeRelations constraints p
    origins   = computeOrigins p q
    conflict  = isNothing $ Multi.consistent origins

-- | Combine multiple examples, checking if there are no conflicts.
combine :: [PolyExample] -> Result [PolyExample]
combine = traverse merge . NonEmpty.groupAllWith (relations &&& inShapes)
  where
    merge :: NonEmpty PolyExample -> Result PolyExample
    merge xs = do
      t <- maybeToError ShapeConflict    $ allSame (outShape <$> xs)
      o <- maybeToError PositionConflict $ consistent (origins <$> xs)
      return (NonEmpty.head xs) { outShape = t, origins = o }

consistent :: NonEmpty Origins -> Maybe Origins
consistent = Multi.consistent . foldl1 Multi.intersection

newtype Result a = Result (Either Conflict a)
  deriving stock (Eq, Ord, Show)
  deriving newtype (Functor, Foldable, Applicative, Monad, MonadError Conflict)

-- TODO: do something with these conflicts.
data Conflict = ShapeConflict | PositionConflict
  deriving stock (Eq, Ord, Show)

------ Pretty ------

instance Pretty PolyExample where
  pretty (PolyExample _ [] t _) = pretty t
  pretty (PolyExample r s t o) =
    barred (inputs : relations) <+> "->" <+> pretty t'
    where
      t' = t <&> \p -> PrettySet $ Multi.lookup p o
      inputs = sep (map prettyMaxPrec s)
      relations = map pretty $ filter relevant r
      barred = encloseSep mempty mempty " | "

instance Pretty (Named PolyExample) where
  pretty (Named name (PolyExample r ss t o))
    | null relations = arguments <+> "=" <+> output
    | otherwise = arguments <+> encloseSep "| " " =" ", " relations <+> output
    where
      arguments = sep (pretty name : map prettyMaxPrec ss)
      relations = map pretty $ filter relevant r
      output = pretty $ t <&> \p -> PrettySet $ Multi.lookup p o

instance Pretty Conflict where
  pretty = viaShow

instance Pretty a => Pretty (Result a) where
  pretty (Result res) = either pretty pretty res
