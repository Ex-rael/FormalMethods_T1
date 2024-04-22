theory problemas
imports Main
begin

primrec soma :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  somaq1: "soma x 0 = x" |
  somaq2: "soma x (Suc y) = Suc (soma x y)"

primrec mult :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  multq1: "mult x 0 = 0" |
  multq2: "mult x (Suc y) = soma x (mult x y)"

lemma soma_add: "soma x y = x + y"
  by (induct y arbitrary: x, simp_all)

theorem mult_1: "\<forall>x y. mult x y = x * y"
proof (rule allI, rule allI, induct_tac y)
  fix x :: nat
  show "mult x 0 = x * 0" by simp
next
  fix x y :: nat
  assume ih: "mult x y = x * y"
  show "mult x (Suc y) = x * (Suc y)"
  proof -
    have "mult x (Suc y) = soma x (mult x y)" by (simp only: mult.simps)
    also have "... = soma x (x * y)" using ih by simp
    also have "... = x + (x * y)" using soma_add by simp
    also have "... = x * (Suc y)" by (simp add: add_mult_distrib2)
    finally show ?thesis .
  qed
qed

theorem mult_2: "\<forall>x::nat. mult x y = mult y x"
proof (induction y)
  show "mult x 0 = 0 x" by (simp)
next
  fix a::nat
  assume HI: "mult "
  show ""
    oops
qed

theorem mult_3: "mult x 1 = x"
proof (induction x)
  show "mult 0 1 = 0" by (simp)
next
  fix a::nat
  assume HI: "mult a 1 = a"
  show "mult (Suc a) 1 = Suc a" by (simp)
qed

theorem mult_4: "mult 1 x = x"
proof (induction x)
  show "mult 1 0 = 0" by (simp)
next
  fix a::nat
  assume HI: "mult 1 a = a"
  have "mult 1 (Suc a) = mult (Suc a) 1" by (simp only: mult_2)
  finally show "mult 1 (Suc a) = (Suc a)" by (simp only: mult_3)
qed

theorem mult_5: "\<forall>x y z::nat. mult x (mult y z) = mult (mult x y) z"
  oops