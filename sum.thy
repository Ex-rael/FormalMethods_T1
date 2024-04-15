theory sum
  imports Main
begin

  primrec sum :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    sum01: "sum x 0 = x" |
    sum02: "sum x (Suc y) = Suc (sum x y)"

  primrec mult :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    mult01: "mult x 0 = 0"| 
    mult02: "mult x (Suc y) = sum x (mult x y)"

theorem mult_commute: "\<forall> x y. mult x y = mult y x"
proof (induction x)
  case nat0:
    show "mult nat0 y = mult y nat0"
    by (simp add: mult01)
  case nat_succ: m
    show "mult (nat_succ m) y = mult y (nat_succ m)"
    proof 
      assume IH: "\<forall> x. mult x y = mult y x"
      show "mult (nat_succ m) y = mult y (nat_succ m)"
      by (simp add: IH mult02 ac [simp del: nat.simps]) (* Use associativity of "+" *)
    qed
qed


theorem mult_assoc: "\<forall> x y z. mult (mult x y) z = mult x (mult y z)"
proof (induction x)
  case nat0:
    show "mult (mult nat0 y) z = mult nat0 (mult y z)"
    by (simp add: mult01 mult.assoc)
  case nat_succ: m
    show "mult (mult (nat_succ m) y) z = mult (nat_succ m) (mult y z)"
    proof
      assume IH: "\<forall> x. mult (mult x y) z = mult x (mult y z)"
      show "mult (mult (nat_succ m) y) z = mult (nat_succ m) (mult y z)"
      by (simp add: IH mult02 mult.assoc)
    qed
qed

theorem mult_one: "\<forall> x. mult x 1 = x"
proof (induction x)
  case nat0:
    show "mult nat0 1 = nat0"
    by (simp add: mult01)
  case nat_succ: m
    show "mult (nat_succ m) 1 = nat_succ m"
    proof
      assume IH: "\<forall> x. mult x 1 = x"
      show "mult (nat_succ m) 1 = nat_succ m"
      by (simp add: IH mult02 ac [simp del: nat.simps]) (* Use associativity of "+" *)
    qed
qed

end
