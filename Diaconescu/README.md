# 選択公理と排中律の周辺のお話
Cubical Agda で Diaconescu の定理の証明を実装することを目標として、寄り道しながら話す予定（寄り道で終わりそう）。

Agda ファイルの html 版 : https://yotsunva.github.io/seminar/Diaconescu/html/

## 08-09
- cubical type theory の最初らへん
  - hcomp
  - transp （今回は使わないので軽め）
- h-level (Hlevel.agda)
  - h-level n → h-level (suc n)
  - isProp (B x) → isProp ((x : A) → B x)
    - function extensionality
  - decidability, stability, constant endofunction
  - Hedberg's theorem
  - isSet Bool

## 08-19
- transp, tt≠ff
- univalence と parametric polymorphism
  - Glue, univalence
  - ¬ LEM∞
- LEM の定式化
- higher inductive type
  - S1
- ¬ (isSet S¹)
  - refl≠loop
  - ¬ LEM∞

## 09-??
- 構成的な選択
- propositional truncation
- index type に条件を課さない選択 (AC?)
  - S1 の連結性
  - ¬ AC?
- AC の定式化

## いつか扱うかもしれない内容
- Diaconescu
  - suspension
  - surjection
- ...
