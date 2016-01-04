/-
Copyright (c) 2015 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/
import .real_limit data.real.complete
open real classical algebra metric_space
noncomputable theory

namespace real

definition diff_quot [reducible] (f : ℝ → ℝ) (x h : ℝ) := (f(x + h) - f(x)) / h

definition deriv_at (f : ℝ → ℝ) (y : ℝ) (x : ℝ) :=
  (diff_quot f x) ⟶ y at 0

definition diff_quot_alt [reducible] (f : ℝ → ℝ) (x y : ℝ) := (f y - f x) / (y - x)

definition deriv_at_alt (f : ℝ → ℝ) (y : ℝ) (x : ℝ) :=
  (diff_quot_alt f x) ⟶ y at x

theorem deriv_alt_is_deriv (f : ℝ → ℝ) (y x : ℝ) : deriv_at f y x ↔ deriv_at_alt f y x :=
  begin
     rewrite [↑deriv_at, ↑diff_quot, ↑deriv_at_alt, ↑diff_quot_alt, ↑converges_to_at],
     apply iff.intro,
     {intros H ε Hε,
     cases H Hε with δ Hδ,
     cases Hδ with δpos Hδ,
     existsi δ,
     split,
     assumption,
     intros x' Hx',
     note Hxx' := Hδ (x' - x),
     rewrite [add.comm at Hxx', sub_add_cancel at Hxx'],
     apply Hxx',
     split,
     apply ne.symm,
     apply sub_ne_zero_of_ne (ne.symm (and.left Hx')),
     rewrite [dist_is_abs, zero_sub, abs_neg, dist_comm at Hx'],
     apply and.right Hx'},
     {intros H ε Hε,
     cases H Hε with δ Hδ,
     cases Hδ with δpos Hδ,
     existsi δ,
     split,
     assumption,
     intros x' Hx',
     note Hxx' := Hδ (x + x'),
     rewrite [add.comm at Hxx', add_sub_cancel at Hxx', add.comm at Hxx'],
     apply Hxx',
     split,
     apply ne_add_of_ne_zero_left,
     apply ne.symm (and.left Hx'),
     rewrite [dist_is_abs, sub_add_eq_sub_sub, sub_self],
     apply and.right Hx'}
   end

theorem deriv_at_unique (f : ℝ → ℝ) (df df' x : ℝ) (H : deriv_at f df x) (H' : deriv_at f df' x) :
        df = df' :=
  begin
    rewrite [↑deriv_at at *, ↑diff_quot at *, ↑converges_to_at at *],
    exact sorry
  end

definition diffable_at [reducible] (f : ℝ → ℝ) (x : ℝ) :=
  ∃ df : ℝ, deriv_at f df x

definition deriv_at_pt (f : ℝ → ℝ) (x : ℝ) (H : diffable_at f x) : ℝ := some H

theorem deriv_at_eq_deriv_at_pt (f : ℝ → ℝ) (x : ℝ) [H : diffable_at f x] :
        deriv_at f (deriv_at_pt f x H) x :=
  some_spec H

theorem diffable_at_iff_ex_deriv_at (f : ℝ → ℝ) (x : ℝ) : diffable_at f x ↔ ∃ y, deriv_at f y x :=
  !iff.refl

definition diffable [class] (f : ℝ → ℝ) :=
  ∀ x, diffable_at f x

definition derivative (f : ℝ → ℝ) [H : diffable f] : ℝ → ℝ :=
  λ x, deriv_at_pt f x !H

--postfix `'`:10 := derivative

theorem cts_of_diffable {f : ℝ → ℝ} {dx x : ℝ} (H : deriv_at f dx x) : continuous_at f x :=
  begin
    rewrite [↑continuous_at],
    apply converges_to_of_sub_converges_to_zero,
    have Hpr : ∀ y, x ≠ y → (y - x) * ((f y - f x) / (y - x)) = (f y - f x), begin
      intros y Hne,
      have Hne' : y - x ≠ 0, from sub_ne_zero_of_ne (ne.symm Hne),
      krewrite [mul_div_cancel' Hne']
    end,
    apply converges_to_at_eq_of_eq_except_at_point,
    rotate 1,
    apply Hpr,
    rewrite [-zero_mul dx],
    apply mul_converges_to_at,
    apply sub_converges_to_zero_of_converges_to,
    apply id_converges_to_at,
    note H' := iff.mp !deriv_alt_is_deriv H,
    rewrite [↑deriv_at_alt at H', ↑diff_quot_alt at H'],
    exact H'
  end

theorem constant_deriv (a x : ℝ) : deriv_at (λ y, a) 0 x :=
  begin
    rewrite [↑deriv_at, ↑diff_quot],
    have H : (λ h : ℝ, 0 / h) = (λ h : ℝ, 0), from funext (λ h, !zero_div),
    rewrite [sub_self, H],
    apply lim_const
  end

theorem constant_diffable [instance] (a : ℝ) : diffable (λ x, a) :=
  begin
    intros,
    existsi 0,
    apply constant_deriv
  end

theorem add_deriv_at_of_deriv_at {f g : ℝ → ℝ} {x df dg: ℝ} (H1 : deriv_at f df x)
        (H2 : deriv_at g dg x) : deriv_at (λ y, f y + g y) (df + dg) x :=
  begin
    rewrite [↑deriv_at at *, ↑diff_quot at *],
    have H : (λ h, (f (x + h) + g (x + h) - (f x + g x)) / h) =
               (λ h, (f (x + h) - f x) / h + (g (x + h) - g x) / h), begin
      apply funext, intro h,
      krewrite [add_sub_comm, -div_add_div_same]
    end,
    rewrite H,
    apply add_converges_to_at,
    repeat assumption
  end

theorem add_diffable_of_diffable [instance] (f g : ℝ → ℝ) [Hf : diffable f] [Hg : diffable g] :
        diffable (λ y, f y + g y) :=
  begin
    intros,
    apply exists.intro,
    note Hf' := some_spec (Hf x),
    note Hg' := some_spec (Hg x),
    apply add_deriv_at_of_deriv_at,
    all_goals assumption
  end

theorem const_mul_deriv_at_of_deriv_at (c : ℝ) (f : ℝ → ℝ) (x df : ℝ) [H : deriv_at f df x] :
        deriv_at (λ y, c * f y) (c * df) x :=
  begin
    rewrite [↑deriv_at at *, ↑diff_quot at *, ↑converges_to_at at *],
    cases lt.trichotomy c 0,
    rotate 1,
    cases a,
    {intros, -- c = 0
    existsi 1,
    split,
    exact zero_lt_one,
    intros,
    krewrite [a, *zero_mul, sub_zero, zero_div, dist_self],
    assumption},
    {intros ε Hε, -- c > 0
    have Hε' : ε / c > 0, from div_pos_of_pos_of_pos Hε a,
    cases H Hε' with δ Hδ,
    existsi δ,
    split,
    exact and.left Hδ,
    intros,
    let Hδ' := and.right Hδ x' a_1,
    krewrite [dist_is_abs, -mul_sub_left_distrib, mul_div_assoc, -mul_sub_left_distrib, abs_mul,
             abs_of_pos a, mul.comm],
    exact mul_lt_of_lt_div a Hδ'},
    {intros ε Hε, -- c < 0
    have Hε' : ε / -c > 0, from div_pos_of_pos_of_pos Hε (neg_pos_of_neg a),
    cases H Hε' with δ Hδ,
    existsi δ,
    split,
    exact and.left Hδ,
    intros,
    let Hδ' := and.right Hδ x' a_1,
    krewrite [dist_is_abs, -mul_sub_left_distrib, mul_div_assoc, -mul_sub_left_distrib, abs_mul,
             abs_of_neg a, mul.comm],
    exact mul_lt_of_lt_div (neg_pos_of_neg a) Hδ'}
  end

theorem const_mul_diffable_of_diffable [instance] (c : ℝ) (f : ℝ → ℝ) [H : diffable f] :
        diffable (λ y, c * f y) :=
  begin
    intros,
    apply exists.intro,
    apply const_mul_deriv_at_of_deriv_at,
    apply some_spec (H x)
  end

theorem id_deriv_at (x : ℝ) : deriv_at (λ y, y) 1 x :=
  begin
    rewrite [↑deriv_at, ↑diff_quot, ↑converges_to_at],
    intros ε Hε,
    existsi 1,
    split,
    exact zero_lt_one,
    intros,
    krewrite [add.comm, add_sub_cancel, div_self (ne.symm (and.left a)), dist_self],
    assumption
  end

theorem id_diffable [instance] : diffable (λ y, y) :=
  begin
    intros,
    apply exists.intro,
    apply id_deriv_at
  end

theorem mul_deriv_at_of_deriv_at (f g : ℝ → ℝ) (df dg : ℝ) (x : ℝ) (Hf : deriv_at f df x)
        (Hg : deriv_at g dg x) : deriv_at (λ y, f y * g y) ((f x) * dg + (g x) * df) x :=
 /- begin
    rewrite [↑deriv_at at *],
    have Hq : (λ h, diff_quot (λ y, f y * g y) x h) =
                    λ h, f (x + h)*((g (x + h) - g x) / h) + g x * ((f (x + h) - f x) / h), begin
     apply funext,
     intro h,
     krewrite [↑diff_quot, -*div_sub_div_same, *left_distrib, -*mul_div_assoc,
              -*neg_mul_eq_mul_neg, *sub_eq_add_neg], -- *add_assoc
     congruence,
     have Hrw :  -(f (x + h) * (g x / h)) + g x * f (x + h) / h = 0, by
       krewrite [-mul_div_assoc]; rewrite [{g x * _}mul.comm, add.comm, -sub_eq_add_neg, sub_self],
     rewrite [-*add.assoc],
     krewrite [ Hrw, zero_add],
     congruence,
     rewrite [mul.comm, mul_div_assoc]
    end,
    have Hq2 : (λ h, f (x + h)*((g (x + h) - g x) / h) + g x * ((f (x + h) - f x) / h))
                  ⟶ (f x * dg+ g x * df) at 0, begin
      apply add_converges_to_at,
      all_goals apply mul_converges_to_at,
      apply lim_add_zero,
      apply cts_of_diffable,
      apply Hf,
      apply Hg,
      apply lim_const,
      apply Hf
    end,
    rewrite Hq,
    apply Hq2
  end-/sorry

theorem mul_diffable_of_diffable [instance] (f g : ℝ → ℝ) [Hf : diffable f] [Hg : diffable g] :
        diffable (λ y, f y * g y) :=
  begin
    intros,
    apply exists.intro,
    apply mul_deriv_at_of_deriv_at,
    apply some_spec (Hf x),
    apply some_spec (Hg x)
  end

set_option pp.coercions true
open nat

-- put this somewhere better
theorem one_real_add_nat (n : ℕ) : (1 : ℝ) + of_nat n = of_nat (succ n) :=
  calc
    (1 : ℝ) + of_nat n = of_nat 1 + of_nat n : rfl
                   ... = of_nat (1 + n) : of_nat_add
                   ... = of_nat (succ n) : one_add

theorem nat_add_one_real (n : ℕ) : of_nat n + (1 : ℝ) = of_nat (succ n) :=
  by rewrite add.comm; apply one_real_add_nat

theorem pow_diffable (n : ℕ) (Hn : n > 0) (x : ℝ) : deriv_at (λ y, y^n) (n*x^(n-1)) x :=
 begin
    induction n,
    apply absurd Hn !not_lt_self,
    induction a,
    have Hid : (λ y : ℝ, y ^ 1) = (λ y, y), from funext (λ y : ℝ, !pow_one),
    have Hid' : 1 * x ^ ((1 : ℕ) - 1) = 1, by rewrite [nat.sub_self, pow_zero, one_mul],
    rewrite [Hid], krewrite [Hid'],
    apply id_deriv_at,
    have Hpow : (λ y : ℝ, y ^ (succ (succ a))) = (λ y : ℝ, y * y ^ succ a),
      from funext (λ y, !pow_succ),
    have IH' : deriv_at (λ y, y ^ succ a) (succ a * x^a) x, begin
      rewrite [-succ_sub_one a at {3}],
      apply v_0_1,
      apply succ_pos
    end,
    let Hprod := mul_deriv_at_of_deriv_at (λ y, y) (λ y, y ^ succ a) 1 (succ a * x^a) x (id_deriv_at x) IH',
    have Hcalc : (x * (of_nat (succ a) * x ^ a) + x ^ succ a * 1) = succ (succ a) * x ^ (succ (succ a) - 1),
      begin
        rewrite [mul_one, succ_sub_one, -mul.assoc, {x*_}mul.comm, mul.assoc, -pow_succ],
        rewrite [-{of_nat (succ (succ a))}nat_add_one_real, right_distrib, one_mul]
      end,
    rewrite [-Hcalc, Hpow],
    exact Hprod
  end

end real
