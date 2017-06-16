/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro

Definitions and properties of gcd, lcm, and coprime.
-/
prelude
import init.data.nat.lemmas init.data.nat.div init.wf init.meta.well_founded_tactics

open well_founded

namespace nat

def gcd : ℕ → ℕ → ℕ
| 0 b     := b
| (a+1) b := have h : b % (a+1) < a+1, from mod_lt _ (succ_pos _), gcd (b%(a+1)) (a+1)

@[simp] theorem gcd_zero_right : Π (x : nat), gcd x 0 = x --:= --congr_fun (fix_eq lt_wf gcd.F 0) x
| 0     := by simp [gcd]
| (a+1) := by simp [gcd]

@[simp] theorem gcd_zero_left (x : ℕ) : gcd 0 x = x := by simp [gcd]

/-theorem gcd_succ_right (x y : ℕ) : gcd x (y+1) = gcd (y+1) (x % (y+1)) :=
begin
wf_induction x; simp [gcd],

end

theorem gcd_succ_right : Π (x y : ℕ), gcd x (y+1) = gcd (y+1) (x % (y+1)) 
| 0 y := by simp [gcd]
| (x+1) y := begin simp [gcd], end
-/

theorem gcd_succ_left (x y : nat) : gcd (x+1) y = gcd (y%(x+1)) (x+1) := 
by simp [gcd]

@[simp] theorem gcd_one_left (n : ℕ) : gcd 1 n = 1 := 
by simp [gcd, mod_one]

theorem one_mod_succ_succ (n : ℕ) : 1 % (n+2) = 1 :=
have 1 < n+2, from lt_of_lt_of_le (lt_succ_self _) (le_add_left _ _),
have ¬ (0 < n+2 ∧ n+2 ≤ 1), from assume h, not_lt_of_ge h.right this,
by rw mod_def; simph

@[simp] theorem gcd_one_right : Π (n : ℕ), gcd n 1 = 1 
| 0 := by simp [gcd]
| 1 := by simp [gcd, mod_one]
| (n+2) := by simp [gcd]; rw [one_mod_succ_succ, gcd_one_left]


/-theorem gcd_succ_right : Π (x y : ℕ), gcd x (y+1) = gcd (y+1) (x % (y+1)) 
| 0 y := by simp [gcd]
| (x+1) y := begin rw [gcd_succ_left y, mod_mod, gcd_succ_right],   end

--begin rw gcd_succ_left y, rw gcd_succ_right ((x+1)%(y+1)%(y+1)), end --rw gcd_succ_right, rw (gcd_succ_left y),  end
--rw [(gcd_succ_right ((y+1)%(x+1)) _)]  end
-/

theorem gcd_def : Π (x y : ℕ), gcd x y = if x = 0 then y else gcd (y % x) x
| 0 y       := by simp [gcd]
| (succ x) y := have h : ¬ succ x = 0, from succ_ne_zero _, by simp [gcd, h]

theorem gcd_self : Π (n : ℕ), gcd n n = n
| 0         := gcd_zero_right _
| (succ n₁) := by simp [gcd_succ_left, add_mod_left, mod_self, gcd] 


theorem gcd_of_pos {m : ℕ} (n : ℕ) (h : m > 0) : gcd m n = gcd (n % m) m :=
let h' := gcd_def m n in
by rw if_neg (ne_of_gt h) at h'; assumption

theorem gcd_rec : Π (m n : ℕ), gcd m n = gcd (n % m) m
| 0 n := by simp [gcd, mod_zero]
| (m+1) n := gcd_of_pos _ (succ_pos _)

/-| 0         := by rw [mod_zero, gcd_zero_left, gcd_zero_right]
| (succ n₁) := gcd_succ _ _-/

/-@[elab_as_eliminator]
theorem gcd.induction {P : ℕ → ℕ → Prop}
                   (m n : ℕ)
                   (H0 : ∀m, P m 0)
                   (H1 : ∀m n, 0 < n → P n (m % n) → P m n) :
                 P m n :=
@induction _ _ lt_wf (λn, ∀m, P m n) n (λk IH,
  by {induction k with k ih, exact H0,
      exact λm, H1 _ _ (succ_pos _) (IH _ (mod_lt _ (succ_pos _)) _)}) m-/


def lcm (m n : ℕ) : ℕ := m * n / (gcd m n)

@[reducible] def coprime (m n : ℕ) : Prop := gcd m n = 1

end nat
