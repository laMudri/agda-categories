import Categories.2-Category
import Categories.2-Functor
import Categories.Adjoint
import Categories.Adjoint.AFT
import Categories.Adjoint.AFT.SolutionSet
import Categories.Adjoint.Alternatives
import Categories.Adjoint.Compose
import Categories.Adjoint.Construction.EilenbergMoore
import Categories.Adjoint.Construction.Kleisli
import Categories.Adjoint.Equivalence
import Categories.Adjoint.Equivalence.Properties
import Categories.Adjoint.Equivalents
import Categories.Adjoint.Instance.0-Truncation
import Categories.Adjoint.Instance.01-Truncation
import Categories.Adjoint.Instance.Core
import Categories.Adjoint.Instance.Discrete
import Categories.Adjoint.Instance.PosetCore
import Categories.Adjoint.Instance.StrictCore
import Categories.Adjoint.Mate
import Categories.Adjoint.Properties
import Categories.Adjoint.RAPL
import Categories.Adjoint.Relative
import Categories.Adjoint.TwoSided
import Categories.Adjoint.TwoSided.Compose
import Categories.Bicategory
import Categories.Bicategory.Bigroupoid
import Categories.Bicategory.Construction.1-Category
import Categories.Bicategory.Extras
import Categories.Bicategory.Instance.Cats
import Categories.Bicategory.Instance.EnrichedCats
import Categories.Category
import Categories.Category.BicartesianClosed
import Categories.Category.CMonoidEnriched
import Categories.Category.Cartesian
import Categories.Category.Cartesian.Properties
import Categories.Category.CartesianClosed
import Categories.Category.CartesianClosed.Canonical
import Categories.Category.CartesianClosed.Locally
import Categories.Category.CartesianClosed.Locally.Properties
import Categories.Category.CartesianClosed.Properties
import Categories.Category.Closed
import Categories.Category.Cocartesian
import Categories.Category.Cocomplete
import Categories.Category.Cocomplete.Finitely
import Categories.Category.Cocomplete.Finitely.Properties
import Categories.Category.Cocomplete.Properties
import Categories.Category.Complete
import Categories.Category.Complete.Finitely
import Categories.Category.Complete.Finitely.Properties
import Categories.Category.Complete.Properties
import Categories.Category.Complete.Properties.Construction
import Categories.Category.Complete.Properties.SolutionSet
import Categories.Category.Concrete
import Categories.Category.Concrete.Properties
import Categories.Category.Construction.0-Groupoid
import Categories.Category.Construction.Arrow
import Categories.Category.Construction.Cocones
import Categories.Category.Construction.Comma
import Categories.Category.Construction.Cones
import Categories.Category.Construction.Coproduct
import Categories.Category.Construction.Core
import Categories.Category.Construction.EilenbergMoore
import Categories.Category.Construction.Elements
import Categories.Category.Construction.EnrichedFunctors
import Categories.Category.Construction.F-Algebras
import Categories.Category.Construction.Fin
import Categories.Category.Construction.Functors
import Categories.Category.Construction.Graphs
import Categories.Category.Construction.Grothendieck
import Categories.Category.Construction.Kleisli
import Categories.Category.Construction.Monoids
import Categories.Category.Construction.ObjectRestriction
import Categories.Category.Construction.Path
import Categories.Category.Construction.Presheaves
import Categories.Category.Construction.Properties.Comma
import Categories.Category.Construction.Properties.EilenbergMoore
import Categories.Category.Construction.Properties.Kleisli
import Categories.Category.Construction.Properties.Presheaves
import Categories.Category.Construction.Properties.Presheaves.Cartesian
import Categories.Category.Construction.Properties.Presheaves.CartesianClosed
import Categories.Category.Construction.Properties.Presheaves.Complete
import Categories.Category.Construction.Properties.Presheaves.FromCartesianCCC
import Categories.Category.Construction.Pullbacks
import Categories.Category.Construction.Thin
import Categories.Category.Core
import Categories.Category.Discrete
import Categories.Category.Duality
import Categories.Category.Equivalence
import Categories.Category.Equivalence.Properties
import Categories.Category.Finite
import Categories.Category.Finite.Fin
import Categories.Category.Finite.Fin.Construction.Discrete
import Categories.Category.Finite.Fin.Construction.Poset
import Categories.Category.Finite.Fin.Instance.Parallel
import Categories.Category.Finite.Fin.Instance.Span
import Categories.Category.Finite.Fin.Instance.Triangle
import Categories.Category.Groupoid
import Categories.Category.Groupoid.Properties
import Categories.Category.Helper
import Categories.Category.Indiscrete
import Categories.Category.Instance.Cats
import Categories.Category.Instance.EmptySet
import Categories.Category.Instance.FamilyOfSetoids
import Categories.Category.Instance.FamilyOfSets
import Categories.Category.Instance.FinCatShapes
import Categories.Category.Instance.FinSetoids
import Categories.Category.Instance.Globe
import Categories.Category.Instance.Groupoids
import Categories.Category.Instance.LawvereTheories
import Categories.Category.Instance.One
import Categories.Category.Instance.PointedSets
import Categories.Category.Instance.Posets
import Categories.Category.Instance.Properties.Cats
import Categories.Category.Instance.Properties.Posets
import Categories.Category.Instance.Properties.Setoids
import Categories.Category.Instance.Properties.Setoids.Cocomplete
import Categories.Category.Instance.Properties.Setoids.Complete
import Categories.Category.Instance.Properties.Setoids.LCCC
import Categories.Category.Instance.Setoids
import Categories.Category.Instance.Sets
import Categories.Category.Instance.Simplex
import Categories.Category.Instance.SimplicialSet
import Categories.Category.Instance.SingletonSet
import Categories.Category.Instance.Span
import Categories.Category.Instance.StrictCats
import Categories.Category.Instance.StrictGroupoids
import Categories.Category.Instance.Zero
import Categories.Category.Lift
import Categories.Category.Monoidal
import Categories.Category.Monoidal.Braided
import Categories.Category.Monoidal.Braided.Properties
import Categories.Category.Monoidal.Closed
import Categories.Category.Monoidal.Closed.IsClosed
import Categories.Category.Monoidal.Closed.IsClosed.Diagonal
import Categories.Category.Monoidal.Closed.IsClosed.Dinatural
import Categories.Category.Monoidal.Closed.IsClosed.Identity
import Categories.Category.Monoidal.Closed.IsClosed.L
import Categories.Category.Monoidal.Closed.IsClosed.Pentagon
import Categories.Category.Monoidal.Construction.Minus2
import Categories.Category.Monoidal.Core
import Categories.Category.Monoidal.Instance.Cats
import Categories.Category.Monoidal.Instance.One
import Categories.Category.Monoidal.Instance.Setoids
import Categories.Category.Monoidal.Instance.Sets
import Categories.Category.Monoidal.Instance.StrictCats
import Categories.Category.Monoidal.Properties
import Categories.Category.Monoidal.Reasoning
import Categories.Category.Monoidal.Symmetric
import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Utilities
import Categories.Category.Product
import Categories.Category.Product.Properties
import Categories.Category.RigCategory
import Categories.Category.SetoidDiscrete
import Categories.Category.Site
import Categories.Category.Slice
import Categories.Category.Slice.Properties
import Categories.Category.Species
import Categories.Category.Species.Constructions
import Categories.Category.SubCategory
import Categories.Category.Topos
import Categories.Category.WithFamilies
import Categories.CoYoneda
import Categories.Comonad
import Categories.Comonad.Relative
import Categories.Diagram.Cocone
import Categories.Diagram.Cocone.Properties
import Categories.Diagram.Coend
import Categories.Diagram.Coequalizer
import Categories.Diagram.Coequalizer.Properties
import Categories.Diagram.Colimit
import Categories.Diagram.Colimit.DualProperties
import Categories.Diagram.Colimit.Lan
import Categories.Diagram.Colimit.Properties
import Categories.Diagram.Cone
import Categories.Diagram.Cone.Properties
import Categories.Diagram.Duality
import Categories.Diagram.End
import Categories.Diagram.End.Properties
import Categories.Diagram.Equalizer
import Categories.Diagram.Equalizer.Indexed
import Categories.Diagram.Equalizer.Limit
import Categories.Diagram.Equalizer.Properties
import Categories.Diagram.Finite
import Categories.Diagram.Limit
import Categories.Diagram.Limit.Properties
import Categories.Diagram.Limit.Ran
import Categories.Diagram.Pullback
import Categories.Diagram.Pullback.Limit
import Categories.Diagram.Pullback.Properties
import Categories.Diagram.Pushout
import Categories.Diagram.Pushout.Properties
import Categories.Diagram.SubobjectClassifier
import Categories.Enriched.Category
import Categories.Enriched.Category.Underlying
import Categories.Enriched.Functor
import Categories.Enriched.NaturalTransformation
import Categories.Enriched.NaturalTransformation.NaturalIsomorphism
import Categories.Enriched.Over.One
import Categories.Enriched.Over.Setoids
import Categories.Functor
import Categories.Functor.Algebra
import Categories.Functor.Bifunctor
import Categories.Functor.Bifunctor.Properties
import Categories.Functor.Cartesian
import Categories.Functor.Cartesian.Properties
import Categories.Functor.Coalgebra
import Categories.Functor.Construction.Constant
import Categories.Functor.Construction.Diagonal
import Categories.Functor.Construction.FromDiscrete
import Categories.Functor.Construction.LiftSetoids
import Categories.Functor.Construction.Limit
import Categories.Functor.Construction.ObjectRestriction
import Categories.Functor.Construction.Zero
import Categories.Functor.Core
import Categories.Functor.Duality
import Categories.Functor.Equivalence
import Categories.Functor.Fibration
import Categories.Functor.Groupoid
import Categories.Functor.Hom
import Categories.Functor.Instance.0-Truncation
import Categories.Functor.Instance.01-Truncation
import Categories.Functor.Instance.Core
import Categories.Functor.Instance.Discrete
import Categories.Functor.Instance.SetoidDiscrete
import Categories.Functor.Instance.StrictCore
import Categories.Functor.Limits
import Categories.Functor.Monoidal
import Categories.Functor.Power
import Categories.Functor.Power.Functorial
import Categories.Functor.Power.NaturalTransformation
import Categories.Functor.Presheaf
import Categories.Functor.Profunctor
import Categories.Functor.Properties
import Categories.Functor.Representable
import Categories.Functor.Slice
import Categories.GlobularSet
import Categories.Kan
import Categories.Kan.Duality
import Categories.Minus2-Category
import Categories.Minus2-Category.Construction.Indiscrete
import Categories.Minus2-Category.Instance.One
import Categories.Minus2-Category.Properties
import Categories.Monad
import Categories.Monad.Duality
import Categories.Monad.Idempotent
import Categories.Monad.Relative
import Categories.Monad.Strong
import Categories.Morphism
import Categories.Morphism.Cartesian
import Categories.Morphism.Duality
import Categories.Morphism.HeterogeneousIdentity
import Categories.Morphism.HeterogeneousIdentity.Properties
import Categories.Morphism.IsoEquiv
import Categories.Morphism.Isomorphism
import Categories.Morphism.Properties
import Categories.Morphism.Reasoning
import Categories.Morphism.Reasoning.Core
import Categories.Morphism.Reasoning.Iso
import Categories.Morphism.Universal
import Categories.Multi.Category.Indexed
import Categories.NaturalTransformation
import Categories.NaturalTransformation.Core
import Categories.NaturalTransformation.Dinatural
import Categories.NaturalTransformation.Equivalence
import Categories.NaturalTransformation.Hom
import Categories.NaturalTransformation.NaturalIsomorphism
import Categories.NaturalTransformation.NaturalIsomorphism.Equivalence
import Categories.NaturalTransformation.NaturalIsomorphism.Functors
import Categories.NaturalTransformation.NaturalIsomorphism.Properties
import Categories.NaturalTransformation.Properties
import Categories.Object.Coproduct
import Categories.Object.Duality
import Categories.Object.Exponential
import Categories.Object.Initial
import Categories.Object.Monoid
import Categories.Object.Product
import Categories.Object.Product.Construction
import Categories.Object.Product.Core
import Categories.Object.Product.Indexed
import Categories.Object.Product.Indexed.Properties
import Categories.Object.Product.Limit
import Categories.Object.Product.Morphisms
import Categories.Object.Terminal
import Categories.Object.Terminal.Limit
import Categories.Object.Zero
import Categories.Pseudofunctor
import Categories.Pseudofunctor.Instance.EnrichedUnderlying
import Categories.Theory.Lawvere
import Categories.Utils.EqReasoning
import Categories.Utils.Product
import Categories.Yoneda
import Categories.Yoneda.Properties
import Relation.Binary.Construct.Closure.SymmetricTransitive
