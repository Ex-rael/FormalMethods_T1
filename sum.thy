theory sum
imports Main
begin

primrec soma :: "nat ⇒ nat ⇒ nat" where
  "soma x 0 = x" |
  "soma x (Suc y) = Suc (soma x y)"

primrec mult :: "nat ⇒ nat ⇒ nat" where
  multq1: "mult x 0 = 0" |
  multq2: "mult x (Suc y) = soma x (mult x y)"

lemma soma_add: "soma x y = x + y"
  by (induct y arbitrary: x, simp_all)

theorem mult_correct: "∀x y. mult x y = x * y"
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


(*-----2-----*)
theorem mult_commutative: "∀x y. mult x y = mult y x"
proof (induction y)
  case 0
    show ?case by (simp add: mult.simps)
  next
  case (Suc k)
    assume IH: "mult x k = mult k x"
    show "mult x (Suc k) = mult (Suc k) x"
    proof -
      have "mult x (Suc k) = mult x k + x" by (simp add: mult.simps)
      also have "... = mult k x + x" using IH by simp
      also have "... = mult (Suc k) x" by (simp add: mult.simps)
      finally show ?thesis .
    qed
qed
end
