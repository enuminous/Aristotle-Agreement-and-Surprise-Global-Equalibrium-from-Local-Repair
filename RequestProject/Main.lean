import Mathlib
import RequestProject.Defs
import RequestProject.Existence
import RequestProject.Contraction
import RequestProject.Potential
import RequestProject.TwoNodeLoop
import RequestProject.Averages
import RequestProject.EqProp
import RequestProject.Layers

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-! Axiom check of the main results. -/
#print axioms RepairNet.exists_equilibrium
#print axioms brouwer_fixed_point
#print axioms Repair.contraction_existsUnique_fixedPoint
#print axioms Repair.relaxation_dist_le
#print axioms Repair.displacement_bounds
#print axioms PotentialRepair.limit_point_is_equilibrium
#print axioms TwoNodeLoop.relaxation_not_tendsto
#print axioms Repair.linear_repair_limit_points
#print axioms EqProp.two_equilibria_give_gradient
#print axioms ObserverConsensus.triangle_no_assignment
