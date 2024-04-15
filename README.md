# Proposta

Construir especificações equacionais recursivas e provas formais por indução no sistema isabelle usando a linguagem ISAR.
Provas em ISAR devem ser o mais detalhadas possível.

Seja a seguinte especificação equacional recursiva para a função que realiza a soma de dois números Naturais no Isabelle: 

```Isabelle
primrec soma::"nat ⇒ nat ⇒ nat" where soma01: "soma x 0 = x"| soma02: "soma x (Suc y) = Suc (soma x y)"
```

Seja a seguinte especificação equacional recursiva para a função que realiza a multiplicação de dois números Naturais no Isabelle. 

```Isabele
primrec mult::"nat ⇒ nat ⇒ nat" where mult01: "mult x 0 = 0"| mult02: "mult x (Suc y) = soma x (mult x y)".
```

Prove, utilizando a linguagem `ISAR`, através da indução, as seguintes propriedades: 

• ∀𝑥, 𝑦 ∈ ℕ. 𝑚𝑢𝑙𝑡(𝑥, 𝑦) = 𝑥 ∗ 𝑦 
• ∀𝑥, 𝑦 ∈ ℕ. 𝑚𝑢𝑙𝑡(𝑥, 𝑦) = 𝑚𝑢𝑙𝑡(𝑦, 𝑥) 
• ∀𝑥 ∈ ℕ. 𝑚𝑢𝑙𝑡(𝑥, 1) = 𝑥 
• ∀𝑥 ∈ ℕ. 𝑚𝑢𝑙𝑡(1, 𝑥) = 𝑥 
• ∀𝑥, 𝑦, 𝑧 ∈ ℕ. 𝑚𝑢𝑙𝑡(𝑥, 𝑚𝑢𝑙𝑡(𝑦, 𝑧)) = 𝑚𝑢𝑙𝑡(𝑚𝑢𝑙𝑡(𝑥, 𝑦), 𝑧)
