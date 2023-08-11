import Mathlib.Tactic

import Mathlib.Data.Int.Basic

import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.Subring.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap

variable {R : Type _} [Ring R] {M : Type _} [AddCommGroup M] [Module R M]

class RightModule (R : Type _) (M : Type _) [Ring R] [AddCommGroup M] where
  rsmul : M -> R -> M
  rsmul_add : rsmul a (r + s) = rsmul a r + rsmul a s
  add_rsmul : rsmul (a + b) r = rsmul a r + rsmul b r
  rsmul_assoc : rsmul (rsmul a r) s = rsmul a (r • s)
  rsmul_one : rsmul a 1 = a

instance comm_ring_right_module
  {R : Type _} [CommRing R]
  {M : Type _} [AddCommGroup M] [Module R M] : RightModule R M where
  rsmul := fun a r => r • a
  rsmul_add := by
    intro a r s
    dsimp
    apply add_smul
  add_rsmul := by
    intro a b r
    dsimp
    apply smul_add
  rsmul_assoc := by
    intro a r s
    dsimp
    rw [mul_comm, smul_smul]
  rsmul_one := by
    intro a
    dsimp
    rw [one_smul]

instance subring_is_module
  {S : Type _} [Ring S]
  {R : Subring S} : Module R S where
  add_smul := by
    intro r s x
    apply add_smul
  zero_smul := by
    intro x
    rw [zero_smul]

def smul_z_module_add_comm_group {A : Type _} [AddCommGroup A] : ℤ -> A -> A :=
    let rec f : ℕ -> A -> A := fun n a =>
      match n with
      | .zero => 0
      | .succ n => a + f n a
    fun n a =>
      match n with
      | .ofNat n => f n a
      | .negSucc n => - (f n a)

instance add_comm_group_is_z_module
  {A : Type _} [AddCommGroup A] : Module ℤ A where
  smul := smul_z_module_add_comm_group

  one_smul := by
    intro b
    unfold HSMul.hSMul; unfold instHSMul; dsimp
    unfold smul_z_module_add_comm_group; simp
    unfold smul_z_module_add_comm_group.f; simp
    unfold smul_z_module_add_comm_group.f; rfl

  mul_smul := by
    intro x y b
    unfold HSMul.hSMul; unfold instHSMul; dsimp
    unfold smul_z_module_add_comm_group; simp
    induction' x with m
    · dsimp
      induction' y with n
      · dsimp
        sorry
      sorry
    sorry

  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

instance add_comm_group_is_right_z_module
  {A : Type _} [AddCommGroup A] : RightModule ℤ A :=
  comm_ring_right_module

-- TODO: group ring RG is left and right R-module
-- TODO: for subgroup H, RG is left and right RH-module

instance subgroup_is_submodule
  (N : AddSubgroup M)
  {p : (r : R) -> (n : N) -> r • n.val ∈ N} : Submodule R M where
  carrier := N.carrier
  add_mem' := by
    intro a b a_in b_in
    apply AddSubsemigroup.add_mem'
    exact a_in
    exact b_in
  zero_mem' := by
    simp
    apply AddSubmonoid.zero_mem'
  smul_mem' := by
    dsimp
    intro c x x_in
    apply p c ⟨x, x_in⟩

def neg_mem''
  {N : Set M}
  (pMul : {r : R} -> (a : N) -> (r • a.val) ∈ N)
  : ∀ {x : M}, x ∈ N → -x ∈ N := by
  intro x x_in
  let ex_smul : (-1 : R) • x = -x := by apply neg_one_smul
  let neg_in : (-1 : R) • x ∈ N := by apply pMul ⟨x, x_in⟩
  apply Set.mem_of_eq_of_mem _ neg_in
  exact Eq.symm ex_smul

def to_add_subgroup
  {N : Set M} (nonempty : Set.Nonempty N)
  (pSub : (a b : N) -> (a.val - b) ∈ N) (pMul : {r : R} -> (a : N) -> (r • a.val) ∈ N)
  : AddSubgroup M where
  carrier := N

  neg_mem' := by
    dsimp
    intro x x_in
    apply neg_mem'' pMul x_in

  add_mem' := by
    intro a b a_in b_in
    let h : -b ∈ N := by apply neg_mem'' pMul b_in
    rw [<- neg_neg b, <- sub_eq_add_neg]
    refine (pSub ⟨a, a_in⟩ ⟨-b, h⟩)

  zero_mem' := by
    dsimp
    let ⟨any, any_in⟩ := nonempty
    let zero_smul : (0 : R) • any ∈ N := by apply pMul ⟨any, any_in⟩
    let zero_eq : (0 : R) • any = 0 := by exact _root_.zero_smul R any
    apply Set.mem_of_eq_of_mem _ zero_smul
    exact Eq.symm zero_eq

instance subset_submodule_mp

  {N : Set M} (nonempty : Set.Nonempty N)
  {pSub : (a b : N) -> (a.val - b) ∈ N} {pMul : {r : R} -> (a : N) -> (r • a.val) ∈ N}
  : Submodule R M := by
  let subgroup := to_add_subgroup nonempty pSub pMul
  have h : subgroup.carrier = N := by rfl
  apply subgroup_is_submodule subgroup
  simp
  intro r a
  show a ∈ subgroup.carrier → r • a ∈ subgroup.carrier
  rw [h]
  intro a_in
  refine pMul ⟨a, a_in⟩

-- TODO: subset_submodule_mpr

def submodule_is_subgroup
  {N : Submodule R M} : AddSubgroup M :=
  { carrier := N
  , add_mem' := by
      intro a b a_in b_in
      apply N.add_mem' a_in b_in
  , zero_mem' := by
      dsimp
      apply N.zero_mem'
  , neg_mem' := by
      dsimp
      intro x x_in
      exact Iff.mpr neg_mem_iff x_in
  }

instance quotient_module
  {N : Submodule R M} : Module R (M ⧸ N) := sorry

section Homomorphism

variable {N : Type _} [AddCommGroup N] [Module R N] {f : M →ₗ[ R ] N }

def ker_is_submodule : Submodule R M where
  carrier := LinearMap.ker f

  add_mem' := by
    intro a b
    simp
    intro fa_ez fb_ez
    rw [fa_ez, fb_ez, add_zero]

  zero_mem' := by
    simp

  smul_mem' := by
    simp
    intro c x fx_ez
    rw [fx_ez, smul_zero]

def im_is_submodule : Submodule R N where
  carrier := LinearMap.range f

  add_mem' := by
    simp
    intro a b x fx_ea y fy_eb
    use x + y
    rw [<- fx_ea, <- fy_eb]
    apply LinearMap.map_add

  zero_mem' := by
    simp
    use 0
    apply LinearMap.map_zero

  smul_mem' := by
    simp
    intro c a
    use c • a
    apply LinearMap.map_smul

-- TODO: coker, coim

def f_injective_iff : Function.Injective f ↔ ∀ x ∈ LinearMap.ker f, x = 0 where
  mp := by
    unfold Function.Injective; simp
    intro fp x fx_ez
    have h := @fp x 0; simp at h
    exact h fx_ez

  mpr := by
    unfold Function.Injective; simp
    intro fp a b fa_eq_fb
    have : f a + (- f b) = 0 := by
      exact Iff.mpr add_neg_eq_zero fa_eq_fb
    have : f a + ((1 : R) • (- f b)) = 0 := by
      rw [<- one_smul R (- f b)] at this
      exact this
    have : f a + (f (-b)) = 0 := by
      rw [smul_neg, <- neg_smul] at this
      rw [<- LinearMap.map_smul f (-1 : R) b] at this
      rw [neg_smul, <- smul_neg, one_smul] at this
      exact this
    have : f (a + -b) = 0 := by
      rw [<- LinearMap.map_add] at this
      exact this
    have : a + -b = 0 := fp (a + -b) this
    apply add_neg_eq_zero.mp this

end Homomorphism
