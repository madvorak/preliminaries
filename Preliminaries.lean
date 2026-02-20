import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs


private class AddMonoid' (M : Type) extends AddSemigroup M, AddZeroClass M

private def AddMonoid'.toAddMonoid {M : Type} (hM : AddMonoid' M) : AddMonoid M where
  nsmul := nsmulRec
  zero_add := hM.zero_add
  add_zero := hM.add_zero

private def AddMonoid.toAddMonoid' {M : Type} (hM : AddMonoid M) : AddMonoid' M where
  zero_add := hM.zero_add
  add_zero := hM.add_zero


private class Monoid' (M : Type) extends Semigroup M, MulOneClass M

private def Monoid'.toMonoid {M : Type} (hM : Monoid' M) : Monoid M where
  one_mul := hM.one_mul
  mul_one := hM.mul_one

private def Monoid.toMonoid' {M : Type} (hM : Monoid M) : Monoid' M where
  one_mul := hM.one_mul
  mul_one := hM.mul_one


private class SubNegMonoid' (G : Type) extends AddMonoid G, Neg G, Sub G where
  sub_eq_add_neg : ∀ a b : G, a - b = a + -b

private def SubNegMonoid'.toSubNegMonoid {G : Type} (hG : SubNegMonoid' G) : SubNegMonoid G where
  zsmul := zsmulRec
  sub_eq_add_neg := hG.sub_eq_add_neg

private def SubNegMonoid.toSubNegMonoid' {G : Type} (hG : SubNegMonoid G) : SubNegMonoid' G where
  sub_eq_add_neg := hG.sub_eq_add_neg


private class DivInvMonoid' (G : Type) extends Monoid G, Inv G, Div G where
  div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹

private def DivInvMonoid'.toDivInvMonoid {G : Type} (hG : DivInvMonoid' G) : DivInvMonoid G where
  div_eq_mul_inv := hG.div_eq_mul_inv

private def DivInvMonoid.toDivInvMonoid' {G : Type} (hG : DivInvMonoid G) : DivInvMonoid' G where
  div_eq_mul_inv := hG.div_eq_mul_inv



private class AddMonoidWithOne' (R : Type) extends AddMonoid R, One R

private def AddMonoidWithOne.toAddMonoidWithOne' {R : Type} (hR : AddMonoidWithOne R) : AddMonoidWithOne' R where

private def AddMonoidWithOne'.toAddMonoidWithOne {R : Type} (hR : AddMonoidWithOne' R) : AddMonoidWithOne R where


private class AddGroupWithOne' (R : Type) extends AddMonoidWithOne R, AddGroup R

private def AddGroupWithOne'.toAddGroupWithOne {R : Type} (hR : AddGroupWithOne' R) : AddGroupWithOne R where
  zsmul z x := if z ≥ 0 then z.toNat • x else - ((-z).toNat • x)
  zsmul_zero' _ := by simp
  zsmul_succ' _ _ := by simp; split; apply succ_nsmul; omega
  zsmul_neg' _ _ := by rfl
  neg_add_cancel := hR.neg_add_cancel
  sub_eq_add_neg := hR.sub_eq_add_neg

private def AddGroupWithOne.toAddGroupWithOne' {R : Type} (hR : AddGroupWithOne R) : AddGroupWithOne' R where
  zsmul := hR.zsmul
  zsmul_zero' := hR.zsmul_zero'
  zsmul_succ' := hR.zsmul_succ'
  zsmul_neg' := hR.zsmul_neg'
  neg_add_cancel := hR.neg_add_cancel
  sub_eq_add_neg := hR.sub_eq_add_neg


private class DivisionRing' (R : Type) extends Ring R, DivInvMonoid R, Nontrivial R where
  mul_inv_cancel : ∀ a : R, a ≠ 0 → a * a⁻¹ = 1
  inv_zero : (0 : R)⁻¹ = 0

private def DivisionRing'.toDivisionRing {R : Type} (hR : DivisionRing' R) : DivisionRing R where
  qsmul q x := ((q.num : R) / (q.den : R)) * x
  nnqsmul q x := ((q.num : R) / (q.den : R)) * x
  mul_inv_cancel := hR.mul_inv_cancel
  inv_zero := hR.inv_zero
  div_eq_mul_inv := hR.div_eq_mul_inv

private def DivisionRing.toDivisionRing' {R : Type} (hR : DivisionRing R) : DivisionRing' R where
  mul_inv_cancel := hR.mul_inv_cancel
  inv_zero := hR.inv_zero
  div_eq_mul_inv := hR.div_eq_mul_inv
