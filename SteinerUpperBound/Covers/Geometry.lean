module

public import SteinerUpperBound.Covers.Geometry.Threshold
public import SteinerUpperBound.Covers.Geometry.Projection
public import SteinerUpperBound.Covers.Geometry.Domination
public import SteinerUpperBound.Covers.Geometry.Persistence
public import SteinerUpperBound.Covers.Geometry.Selected

@[expose] public section

/-!
# Deterministic threshold geometry for retained terminal covers

`SteinerUpperBound.Covers.Geometry` uses strict metric threshold graphs on
explicit finite subsets. This module has no dependency on `Structural`.
`Covers.Geometry.Structural` separately bridges the concrete definitions and
proves domination of `Structural.rowSaving`.
-/
