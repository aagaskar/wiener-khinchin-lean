# Wiener–Khinchin theorem in Lean

This project formalizes the spectral-measure form of the continuous-time
Wiener–Khinchin theorem in Lean 4 using mathlib.

## Statement

Let $X(t)$ be a complex-valued, wide-sense stationary process on a probability
space. Each $X(t)$ is square-integrable, the mean is constant, and the
autocorrelation $\mathbb{E}[X(t)\overline{X(s)}]$ depends only on the time
difference $t-s$. Write the lag autocorrelation as

$$
r(\tau) = \mathbb{E}[X(\tau)\overline{X(0)}].
$$

If $r$ is continuous, there is a unique finite positive Borel measure $\nu$ on
the real line such that for every lag $\tau$,

$$
r(\tau) = \int_{\mathbb{R}} e^{2\pi i\tau\xi}\,d\nu(\xi).
$$

The measure $\nu$ assigns power to frequency bands and has total mass $r(0)$.
When $\nu$ has a density with respect to Lebesgue measure, that density is the
power spectral density. The factor $2\pi$ expresses frequency $\xi$ in cycles per
unit time.

## Lean formalization

`WienerKhinchin` names the proposition, and `wiener_khinchin` proves it.
The existence proof uses Plancherel to construct spectral measures from finite
observation windows, then takes a weak limit using tightness and Prokhorov's
theorem. Uniqueness follows because a finite measure is determined by its
characteristic function. [Lean statement and proof](WienerKhinchinLean/Basic.lean)