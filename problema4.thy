theory problema4
imports Main
begin

primrec soma :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  somaq1: "soma x 0 = x" |
  somaq2: "soma x (Suc y) = Suc (soma x y)"

primrec mult :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  multq1: "mult x 0 = 0" |
  multq2: "mult x (Suc y) = soma x (mult x y)"

theorem mult_4: "\<forall>x::nat. mult x 1 = x"
proof (induction x)
  fix a::nat
  have "mult a (Suc 0) = soma a (mult a 0)" by (simp only: multq2)
  also have "... = soma a 0" by (simp only: multq1)
  also have "... = a" by (simp only: somaq1)
  finally show "mult a (Suc 0) = a" by (simp)
qed

(* theorem multv1: "\<forall>(x y)::(nat nat). mult x y = x * y"
proof (induction y)
  show "\<forall>x::nat. mult x 0 = x * 0"
  proof (rule allI)
    fix a::nat
    have "mult a 0 = 0" by (simp only: multq1)
    also have "... = a * 0" by (arith)
    finally show "mult a 0 = a * 0" by (simp)
  qed
next
  fix b::nat
  assume HI: "\<forall>x::nat. mult x b = x * b"
  show "\<forall>x::nat. mult x b = x * b"
  proof (rule allI)
    fix a::nat
    have "mult a (Suc b) = soma b (mult a b)" by (simp only: multq1)
    also have "... = b + (a * b)" by (simp only: HI)
    finally show "mult a (Suc b) = b + (a * b)" by (simp)
  qed
qed *)