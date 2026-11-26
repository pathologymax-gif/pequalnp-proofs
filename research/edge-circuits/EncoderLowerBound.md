# A 16-to-4 one-hot binary encoder needs exactly 22 gates

Consider a Boolean circuit with gates of fan-in at most two, free input wires, arbitrary fan-out and $m$ specified output wires. Write $y_0$ for the output vector on the all-zero input. Choose $n$ one-hot inputs whose output vectors are pairwise distinct and differ from $y_0$. The circuit has at least $2(n-m)$ gates. The bound applies to gates with arbitrary Boolean truth tables, including constants and unary gates. The choice of output wires can include intermediates and repeated wires.

## Proof

Keep a set $D$ of distinct wires, starting with the outputs. For each chosen one-hot input record the subset of $D$ whose values differ from their values at zero. Throughout the argument these records are nonempty and pairwise distinct. This follows whenever the values on $D$ determine all original outputs, since a Boolean bit that differs from its fixed baseline has a unique possible value.

Walk through the gates in reverse evaluation order. A gate whose output wire is absent from $D$ needs no action. Otherwise remove its output $w$ from $D$, then insert its distinct operand wires. Values on the new set determine values on the old set. If the gate language reads a missing or forward wire as false, omit that occurrence, since its value is already known. Missing output wires can be omitted at the start for the same reason.

Let $s(D)$ count singleton records and use the potential $|D|+s(D)$. Let $r$ be the number of operands already in $D\setminus\{w\}$. The change in $|D|$ is at most $1-r$. Suppose a record becomes a singleton after previously containing at least two wires. It changed $w$, since all other old coordinates remain. It also changed at least one surviving old wire $u$. Since $w$ changed, some operand changed. There is now just one changed coordinate, so that operand must be $u$. It is one of the $r$ already-present operands. Distinct new singleton records have distinct $u$, so at most $r$ records become singletons. The potential increases by at most one per gate.

Initially $|D|+s(D)\le 2m$. Finally $D$ consists entirely of raw inputs. Every chosen one-hot input must have its own raw wire in $D$ and its record is a singleton. The final potential is at least $2n$. This proves the bound.

## The encoder

For the positive binary encoder, on the 16 inputs indexed by $p=0,\ldots,15$ the four output wires must encode the bits of $p$. These vectors exhaust all four-bit vectors. Whatever the output at zero, exactly 15 of the specified vectors differ from it. The bound gives $2(15-4)=22$. The public statement asking for a circuit with at most 21 gates is therefore false. The theorem `PEqualNP.EncoderConclusion.no_encoder_21` proves the exact negation in Lean. The independent research file uses the project circuit definitions and was checked with Lean 4.36.

For a matching upper bound, associate one wire to every nonempty subset of the four bit positions. Feed $x_S$ into the wire for $S$. For every nonsingleton $S$, send its combined signal to the wires for its least singleton and its remaining subset; process larger subsets first and OR all signals arriving at each wire. A singleton bit wire receives $x_S$ exactly when its bit lies in $S$. The eleven nonsingletons send 22 signals in total. There is already one raw term at each destination, so exactly 22 binary ORs combine them.

For comparison, a monotone circuit can realize all four positive bits and all four complemented bits in 32 gates. Arrange the inputs in a four-by-four grid. Build each of its four row unions and four column unions using three gates, then use one OR per output to combine the appropriate two row or column unions. The argument above does not establish the minimum for this eight-output problem.

[EncoderSixteen.lean](EncoderSixteen.lean) proves the lower bound and both constructions. [verify_encoders.py](verify_encoders.py) builds both circuits and checks their sixteen inputs. The public statements are [the four-output encoder](https://pequalnp.com/lemma#L-meta-19061) and [the eight-output encoder](https://pequalnp.com/lemma#L-meta-19060).
