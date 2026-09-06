# Proof of the sharp Motzkin-root theorem

Define M₀=M₁=1 and (n+3)Mₙ₊₁=(2n+3)Mₙ+3nMₙ₋₁ for n≥1. Define T₀=1 and Tₙ₊₁=Mₙ₊₁−Tₙ. Induction identifies T with the alternating sum.

## The ratio enclosure

Put
\[
x_k=\frac{M_{k+1}}{M_k},\qquad y_k=\frac{T_{k+1}}{T_k},
\qquad b_k=\frac{3(k+1)}{k+5/2}.
\]
We need
\[
b_k\le y_k\le b_{k+2}\qquad(k\ge9). \tag{1}
\]

First let \(f_k(t)=(2k+3)/(k+3)+3k/((k+3)t)\), so \(x_k=f_k(x_{k-1})\).
This function decreases on \(t>0\), and direct algebra gives
\[
f_k(b_k)-b_k=\frac{3(k-2)}{2(k+3)(k+1)(2k+5)},
\]
\[
b_{k+1}-f_k(b_{k-1})=\frac{9}{2(k+3)(2k+7)}.
\]
Starting from \(x_2=2=b_2<b_3\), induction yields
\(b_k\le x_k\le b_{k+1}\) for all \(k\ge2\).

The alternating-sum definition gives
\[
T_{k+1}=(x_k-1)T_k+x_kT_{k-1},\qquad
y_k=x_k-1+\frac{x_k}{y_{k-1}}. \tag{2}
\]
Here \(T_2=T_3=2\); since \(x_k\ge b_k\ge2\) for \(k\ge2\), the first recurrence proves \(T_k>0\) for all \(k\ge2\).

We next prove \(x_k\le y_k\le x_{k+1}\) for \(k\ge9\).
The base case follows by cross-multiplication from
\[
x_9=\frac{2188}{835}<y_9=\frac{1586}{602}<x_{10}=\frac{5798}{2188}.
\]
Suppose the enclosure holds at \(k\ge9\). Equation (2) gives
\(y_{k+1}\ge x_{k+1}\) and
\[
y_{k+1}-x_{k+2}\le
x_{k+1}-1+\frac{x_{k+1}}{x_k}-x_{k+2}=H_k(x_k),
\]
where
\[
H_k(t)=f_{k+1}(t)-1+\frac{f_{k+1}(t)}{t}
-f_{k+2}(f_{k+1}(t)).
\]
To see that \(H_k\) decreases, write \(f_{k+1}(t)=A+B/t\) and \(f_{k+2}(t)=C+D/t\), with all four constants positive. Then
\[
H_k(t)=A-1-C+\frac{A+B}{t}+\frac{B}{t^2}-\frac{Dt}{At+B}.
\]
Each nonconstant term has negative derivative for \(t>0\). Hence
\[
H_k(x_k)\le H_k(b_k)
=-\frac{3(4k^2-13k-53)}{4(k+1)(k+4)(k+5)(2k+5)}<0
\quad(k\ge9).
\]
The numerator polynomial is positive at 9 and increasing thereafter. This closes the induction. Combining the two enclosures proves (1).


## The logarithmic tail used in Lean

Let K=3¹²/T₁₂=531441/11299. Since yₖ≤3 for k≥9, induction gives log Tₙ≤n log 3−log K for n≥12. Also log K>15/4: K>32·(7/5), log(7/5)≥2/7, and a rational lower bound for log 2 proves this strictly. This constant comparison is fully formalized in `MotzkinAnalysis.log_constant`.

Put p=yₙ₋₁ and q=yₙ. The ratio enclosure gives

- n(log p−log 3)≥−3/2;
- n(n−1)(log q−log p)≤9/2.

These follow from log(1+u)≤u and q/p≤1+9/[n(2n+9)]. Multiplying the desired logarithmic concavity expression by n(n²−1) yields

Dₙ = 2(n log p−log Tₙ) − n(n−1)log(q/p) ≥ 2 log K−15/2 > 0.

This proves the claim at every center n≥12. For centers 6 through 11, exact integer arithmetic proves

Tₙ^[2(n²−1)] > Tₙ₋₁^[n(n+1)] Tₙ₊₁^[n(n−1)].

The relevant values T₄ through T₁₂ are 7, 14, 37, 90, 233, 602, 1586, 4212, 11299. At center 5 the inequality strictly reverses. The modules `MotzkinFinite` and `Motzkin` check these finite powers in the kernel. Taking positive roots establishes strict log-concavity of rₙ from index 5, and the failed center 5 rules out starting at index 4 or earlier.

The generic analytic module has explicit hypotheses; `MotzkinTheorem` discharges them for the recurrence-defined sequence. No enclosure or desired inequality remains assumed by the exported theorems.
