.PHONY: cache build axioms

# Download the prebuilt Mathlib oleans (run once, before the first build).
cache:
	lake exe cache get

build:
	lake build

axioms:
	lake env lean AxiomCheck.lean
