# A binary proof of the odd-position formula for A232895

The sequence and position formula are listed in [OEIS A232895](https://oeis.org/A232895) and [OEIS A232896](https://oeis.org/A232896). The proof and Lean formalization are complete.

## Theorem

Let G_1=(1,2). To construct G_(n+1), read G_n from left to right and propose x+2, then 2x, for each entry x, keeping only integers not previously encountered (including earlier proposals in this generation). Let S be the concatenation of the generations. With F_0=0, F_1=1, the one-based position of 2n-1 in S is

    n - 1 + F_(n+1),  for every n >= 1.

In fact, the members of generation n are exactly the odd integer 2n-1 and the even integers 2m satisfying

    bit_length(m) + popcount(m) = n + 1.

The odd integer is the first entry of that generation.

## 1. Generations are shortest-path layers

Consider the directed graph on positive integers with edges x -> x+2 and x -> 2x. Put both 1 and 2 at distance zero. The rule defining the generations is breadth-first search with duplicate deletion, so G_n contains exactly the vertices at distance n-1 from {1,2}. This follows by induction: every new child has distance at most n, and every vertex at distance n has a predecessor at distance n-1 and has not occurred earlier.

Once a path becomes even, it remains even. Thus an odd integer 2n-1 can only be reached from 1 by n-1 additions of 2. It is the only odd integer in G_n. Moreover, it is first: this holds in G_1, and its +2 child is the first proposed child in G_(n+1), and is a new odd integer.

## 2. Starting at 1 does not shorten an even path

Any path from 1 to an even integer has a first doubling. Immediately before that doubling its value is 2r+1, reached by r additions of 2. Its initial segment therefore reaches 4r+2 in r+1 steps.

If r=0, this initial segment reaches the other seed 2, and can be discarded. If r>=1, start instead at 2, add 2 exactly r-1 times to reach 2r, double to 4r, and add 2 to reach 4r+2. This uses r+1 steps, exactly as many as the original initial segment. Append the rest of the original path.

Consequently the shortest distance from {1,2} to an even integer is the shortest distance from 2 alone. Dividing every vertex of an even path by 2 turns its two operations into m -> m+1 and m -> 2m, with initial value 1.

## 3. Shortest add-or-double paths

For m>=1, let L(m) be its binary length, s(m) its number of binary ones, and W(m)=L(m)+s(m)-2. The minimum number of operations +1 and doubling needed to reach m from 1 is W(m).

For the upper bound, start with the leading binary 1 and read the remaining bits of m. For each bit, double; if that bit is 1, also add 1. This uses L(m)-1 doublings and s(m)-1 additions, hence W(m) operations.

For the lower bound, W(1)=0 and neither allowed operation can increase W by more than 1. Doubling appends a zero and increases W by exactly 1. For incrementing, if m is not all ones in binary and has t trailing ones, the length is unchanged and the number of ones changes by 1-t, so W(m+1)-W(m)=1-t<=1. If m consists of L ones, incrementing changes length from L to L+1 and the number of ones from L to 1, giving a change of 2-L<=1. Thus after k operations the value of W is at most k, proving the lower bound.

Sections 1-3 show that 2m belongs to G_n exactly when W(m)=n-1, or L(m)+s(m)=n+1.

## 4. Count binary strings

The leading 1 contributes 2 to L(m)+s(m). Each subsequent binary 0 contributes 1 and each subsequent binary 1 contributes 2. Thus the even members of G_n correspond bijectively to finite binary suffixes of total weight n-1, with weights 1 for 0 and 2 for 1.

Let c_k be the number of such suffixes of total weight k. There is one empty suffix, so c_0=1; only the suffix 0 has weight 1, so c_1=1. For k>=2, separating suffixes by their final bit gives c_k=c_(k-1)+c_(k-2). Therefore c_k=F_(k+1), and G_n has F_n even entries and one odd entry.

Since the odd entry is first, its position is

    1 + sum_(j=1)^(n-1) (1 + F_j)
      = n + (F_(n+1)-1)
      = n - 1 + F_(n+1).

This includes n=1 by the empty-sum convention. QED.

## Scope and limitations

The argument proves the stated formula for every n; finite computations check examples. The formula is a corollary of [Kimberling–Moses's tree theorem](https://www.mathstat.dal.ca/FQ/Papers1/52-5/Kimberling.pdf).
