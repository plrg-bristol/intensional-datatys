# Intensional Constraints

The pattern-match safety problem is to verify that a given functional program will never crash due to nonexhaustive
patterns in its function definitions. This tool is designed to prevent this type of crash.

For each top-level definition a set of __constraints__ are inferred, these are both flow and context sensitive.
The constraints are in terms of __refinement variables__ which approximately refer to a single point in the function definition.

## Usage

The tool is a plugin for GHC, and therefore directly integrated into the compilation processes.
To add this analysis as another stage to compilation:

  1. Download this repository
  2. Add ``path/to/intensional-constraints`` to your ``cabal.project`` file in the ``packages` stanza
  3. Add ``-fplugin=Lib`` to the ``ghc-options`` field, and ``intensional-constraints`` to the ``build-depends`` field.
  
### Troubleshooting 

As this is only a prototype tool, it's interface and deployment is underdeveloped.
If you wish to run the tool on a package which it depends, i.e. the ``containers`` pacakge, cabal will consider this case as a cyclic dependency.
To circumnavigate this issue we recommend changing the name of the package on which you wish to run the tool, or holding out for a better interface!
  
## The Taxonomy of Constraints

The constraints produced by analysis have two components: a guard (on the left of the question mark), and the body on the right, corresponding to context sensitivity and flow sensitivity respectively.

   - ``k in X ? X >- Y``

As it stands there is no explicit error reporting, however, unsatisfiable constraints are immediately identifiable:

   - ``k in {}``
