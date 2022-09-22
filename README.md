# QuCalc
Welcome to QuCalc, the quantum computation package for Mathematica 4.0.

Author: Paul Dumais, dumais@iro.umontreal.ca

"Mathematica" is a registered trademark of "Wolfram Research".  QuCalc
may and must be distributed freely.  It must be distributed without
modifications, including the name of the authors and this message.

##  General remarks 

QuCalc is a Mathematica package whose pupose is to simulate and solve
problems related to quantum computing.  QuCalc has been developed by
Paul Dumais at Laboratoire d'informatique théorique et quantique
(Montréal University) and at the Crypto and Quantum Info Lab (McGill
University).

A minimal knowledge of Mathematica is required in order to use the
QuCalc package effectively. It is useful to recall that Mathematica
does not incorporate in its kernel a data type for matrices: instead,
one must use a "list of lists" to represent matrices. It is strongly
recommended to carry out and analyze the examples suggested in the
help sections of the this package. These examples form an essential
complement to the main help text.

The paradigm adopted for the QuCalc Mathematica package is that of
converting states and operators into vectors and matrices. Kets are
represented as column vectors written in the canonical basis (i.e. the
basis into which the Pauli operator \sigma_z is diagonal); unitary
transformations are represented as square matrices; mixed states
correspond to density matrices; etc.

The identifiers defined when QuCalc is loaded in Mathematica all begin
with lowercase letters. Following standard usage, identifiers
beginning with a capital letter are those of Mathematica.  Some
identifiers of Mathematica are also overloaded in QuCalc such as
"CircleTimes".

Whenever you don't know how to interpret a result x returned by
QuCalc, try FullForm[x]. This will tell you how QuCalc "interprets"
the result.  If x appears more complicated than it should be, test on
it several simplification tools included in Mathematica, such as
Simplify[x], FullSimplify[x], TrigReduce[x], ComplexExpand[x], ...

In general, functions do not test their inputs. When invalid inputs
are supplied to a function, the result is not defined (error message
from Mathematica, bizarre answer, etc.).


## General information

Mathematica identifiers overloaded in QuCalc:
	CenterDot       CircleDot       CirclePlus      CircleTimes
	Dot             OverBar         OverTilde       \[Placeholder]
	Power           Subscript       SuperDagger     Vee
	Wedge

Data types:
	ens             ket             schmidt         sqo
	state           supop           unit

Tests:
	ensQ            ketQ            sqoQ            stateQ
	supopQ          unitQ

Constants:
	bb84            cnot            knot            mm
	mmm             not             phim            phip
	psim            psip            sigx            sigy
	sigz            wh              xm              xp
	ym              yp              zm              zp

Functions:
	anc             band            bits            block
	bnot            bor             bscal           bxor
	circuit         cycle           ctrl            dag
	dotexp          eigen           eigenVal        eigenVect
	entropy         fgate           fidelity        fourier
	gate            id              kron            krondiv
	kronexp         ktrl            lvNorm          lvProd
	maxmix          phase           randomUnit      regAnc
	regGet          regOper         regSet          regState
	regTrout        rotx            roty            rotz
	swap            trout           unvec           vec

## Functions

Dot[x, y, ...]
x.y. ...
	Dot gives the product (composition, application) of its arguments.
	The arguments may be in the form of matrices, "ket", "unit",
	"state", etc, as long as the product is defined.

	Note that if u is a "unit" and r is a "state", then u.r returns the
	density matrix resulting from the application of u on r. Do not type
	u.r.dag[u].

	Try:
		dag[xp] . zp
		sigz . zm
		sigz . sigz
		wh . state[zm]
		mmm . xp
		wh . mm . wh

OverBar[x]
	Returns the complex conjugate of x. It is equivalent to the
	Mathematica function "Conjugate".

	This function can be entered using 2D notation by typing:
	"CTRL-&" "_".

	Try:
		OverBar[I]

anc[nA, nB, nC]
	Returns a data structure of type "sqo" representing the
	operation of adding a constant ancillary state |0> of
	dimension nB in between two Hilbert spaces of dimensions nA
	and nC.

	Try:
		r = anc[2,2,2] . ket["11"]

eigen[r]
band[s1, s2, ...]
Wedge[s1, s2, ...]
	Performs a bitwise "and" operation over binary strings, i.e.,
	lists of 0's and 1's.

	This function may be entered in infix notation using the
	operator "Wedge" of Mathematica, by typing: "ESC" "^" "ESC".

	Try:
		band[{0,1,1,1}, {0,0,1,1}]





bb84
	Constant of type "ens" representing a statistical ensemble of 4
	equiprobable states corresponding to the qubits 0 and 1 written in
	the canonical and diagonal bases.

	Try:
		bb84
		wh . bb84
		state[bb84]





bits[x, n]
	Converts the integer x into its corresponding binary
	expression (list of 0's and 1's).

	Try:
		ket[bits[5,3]]
		ket[bits[5,4]]





block[u, v]
	Block product of the unitary transformations u and v.

	Try:
		block[wh, wh]

	See also:
		kron, unit




bnot[s]
OverTilde[s]
	Returns the binary complement (negation) of a bit list.

	This function can be entered in 2D notation by typing:
	"CTRL-&" "~".

	Try:
		bnot[{0,1,0}]

	See also:
		band, bits, bor, bscal, bxor




bor[s1, s2, ...]
Vee[s1, s2, ...]
	Performs a bitwise "or" operation over bit lists.

	This functions can be called in "infix" notation using the
	Mathematica operator "Vee" by typing: "ESC" "v" "ESC".

	Try:
		bor[{0,1,1,1}, {0,0,1,1}]





bscal[s1, s2]
CircleDot[s1, s2]
	Returns the boolean scalar product of the binary lists s1 and
	s2.

	This function can be called using the Mathematica infix
	operator "CircleDot", by typing: "ESC" "c" "." "ESC".

	Try:
		bscal[{0,1,1,1}, {0,0,1,1}]

	See also:
		band, bits, bnot, bor, bxor




bxor[s1, s2, ...]
CirclePlus[s1, s2, ...]
	Returns the result of a bitwise "exclusive or" operation
	performed over bit lists.

	This function may be called in infix notation using the
	Mathematica operator "CirclePlus" by typing: "ESC" "c" "+"
	"ESC".

	Try:
		bxor[{0,1,1,1}, {0,0,1,1}]





circuit[m]
	This function performs a series of compositions and Kronecker
	products associated with the elements of the matrix m. The
	lines of m represent the quantum wires which carry qubits from
	left to right.  The columns of m represent the quantum gates
	to be applied on qubits.  In other words, the matrix m is a
	gate array.

	For example, circuit[{{wh,id[]}, {not,not}}] returns a data
	structure of type "unit" (a unitary transformation) equivalent
	to a circuit of two gates acting on two quantum wires. The
	first wire is tranformed by a Walsh-Hadamard (wh) operation
	followed by a negation (not) operation. The second wire, is
	left unchanged by the first identity (id[]) operation, and is
	then negated by a "not" operation.

	To build a gate acting coherently on a subset of selected
	qubits (leaving unchanged the rest of the qubits), place the
	desired transformation on the last qubit of the selected
	subset in question. The other wires are assigned integers
	describing a "chained list" in top-down order.  For example,
		circuit[{{id[]},{1},{3},{id[]},{id[]},{ctrl[ctrl[not]]}}]
	represents a Toffoli gate (ctrl[ctrl[not]]), acting on the 2nd, 3rd
	and 6th wires of a quantum circuit of 6 qubits.

	The function "circuit" is very useful when combined with the
	2D notation of Mathematica commonly used to create matrices:
	"CRTL-RETURN" to create the lines, and "CTRL-," to create the
	columns. In that case, the circuit entered in Mathematica
	looks exactly as in standard gate array notation. Note also
	that the "Placeholder" of Mathematica (the little blank square
	appearing in 2D notation), stands for the identity
	transformation. It is thus unnecessary to fill out all the
	entries of a circuit.

	Try:
		circuit[{{ 1,     1,   1  },
		         {cnot, knot, cnot}}]

		circuit[{{ 1,   mm},
		         {cnot, mm}}]





phim
phip
psim
psip
xm
xp
ym
yp
zm
zp
	Constants of type "ket".

	phim, phip, psim, psip: Bell's states.

	xm, xp, ym, yp, zm, zp: Pure states corresponding to the poles and
	the 4 cardinal points on the equator of the Bloch-Poincaré sphere.

	Try:
		cnot . kron[wh, id[]] . ket["00"] == phip





cnot
knot
not
sigx
sigy
sigz
wh
	Constants of type "unit".

	cnot: controled-not;
	knot: inversed controled-not;
	not: negation (of 1 qubit);
	sigx, sigy, sigz: Pauli matrices;
	wh: Walsh-Hadamard transformation.

	Try:
		not == sigx





ctrl[u]
ctrl[n, u]
ktrl[u]
	Various forms of controlled gates (conditional operations).

	ctrl[u]: controlled u gate;
	ctrl[n,u]: u gate controlled by n wires;
	ktrl[u]: inverted controlled u gate.

	Try:
		ctrl[not] == cnot
		ctrl[2,not]
		ktrl[wh]





cycle[n,i,j]
	Unitary transformation acting on n qubits which performs a circular
	permutation of the qubits i to j (in top-down order).

	Try:
		c = cycle[3,1,3]
		c . ket["010"] == ket["001"]
		Power[c,2] == dag[c]

	See also:
		circuit




dag[x]
SuperDagger[x]
	Returns the conjugate transpose of x.

	This function can be called in 2D notation by typing:
	"CTRL-^" "ESC" "d" "g" "ESC".

	Try:
		dag[wh] == wh




dotexp[x, n]
Power[x, n]
x^n
	These operators return the result of the n-fold product x.x. ... .x.
	The argument x can be of type "unit", "supop", "sqo", etc., as long
	as the result is meaningful.

	Try:
		Simplify[rotx[t]^3]




eigen[r]
eigenVal[r]
eigenVect[r]
	Returns the eigenvalues and eigenvectors of a state.

	eigen[r]: returns a statistical ensemble (type "ens") formed with
	all the pairs eigenvalues-eigenvectors of r.

	eigenVal[r]: returns a diagonal matrix whose elements are the
	eigenvalues of the state r, in the data type "state".

	eigenVect[r]: returns a unitary matrix whose columns are the
	eigevectors of r.

	Try:
		eigen[maxmix[2]]
		eigenVect[state[xp]]
		eigenVal[state[xp]]
		eigen[state[yp]] == yp
		eigen[bb84]
		eigen[state[bb84]]





ens[...]
	Data type representing a statistical ensemble of states.

	A valid "ens" object contains a list of pairs {p,r} where p is
	a real number between 0 and 1 (a probability), and r is an
	object of type "ket" or "state". The p's must add to unity.

	An "ens" object containing a trivial list of only one pair {p,r}
	with p=1 is automatically converted to a "state" or "ket" r.

	Try:
		bb84
		FullForm[bb84]
		mmm . xp
		FullForm[mmm . xp]
		eigen[maxmix[2]]
		FullForm[eigen[maxmix[2]]]

	See also:
		bb84, eigen, ensQ, ket, state, sqo




entropy[r]
	Numerical calculation of the von Neumann entropy of the state r.

	Try:
		entropy[state[bb84]]





fgate[m, n, f]
	Returns a unitary transformation, acting on m+n qubits, that
	is equivalent to the function f acting on classical inputs.

	The function f is a Mathematica "pure function". It takes on
	input m bits and must return a list of n bits. Thus, f can be
	seen as a (classical) function of m bits to n bits.

	On a pure canonical basis state |x,y>, fgate leaves the first
	m qubits |x> unchanged, and transforms the last n qubits |y>
	into |y XOR f(x)> where XOR stands for the exclusive or of two
	n bit strings.

	Try:
		fgate[1,1,({#})&]
		fgate[1,2,({(#), (#)})&]





fidelity[r1, r2]
	Numerical calculation of the fidelity function of two (pure or
	mixed) states.

	Try:
		fidelity[zp, xp]





fourier[m]
	m-dimensional Fourier transform.

	Try:
		fourier[4]

	See also:
		circuit




gate[n, b, f]
gate[n, f]
	Returns a unitary transformation of dimension b^n (2^n if b is
	ommitted) described by the function f.

	The function f is a Mathematica "pure function". It takes as
	input n integers between 0 and b-1, and returns a "ket". For
	different values in its arguments f must return orthogonal kets.

	Try:
		gate[2,(ket[{#1, bxor[#1,#2]}])&]

	See also:
		circuit, fgate




id[n]
id[]
	Identity transformation on n qubits (1 if n is ommited).

	Try:
		id[8]





ket[...]
	Data type representing a pure state.

	A well-defined "ket" contains a matrix of dimension n x 1, and must
	be of norm 1.

	Note that in 2D notation, lines of a matrix can be created using
	"CTRL-RETURN".

	To obtain a "bra" from a "ket", use dag[ket[...]]. There is no
	data type "bra" in QuCalc.

	The expression ket[0] (or ket[1]) is converted in such a way to
	represent the bit 0 (or 1) in the canonical basis of a 2-dimensional
	Hilbert space, i.e., a qubit. To obtain a register of many qubits,
	one can concatenate several bits into a list or into a character
	string. To obtain a quantum register whose dimension is a power
	not reducible in base 2, one can add as a subscript the value of the
	base in question. See the examples below.

	In 2D notation, "Subscript[x,y]" may be entered by typing: "x"
	"CTRL-_" "y".

	Try:
		ket[0]
		FullForm[ket[0]]
		FullForm[ket[0][[1]]]
		ket[{0,1,0}]
		ket["010"]
		ket[Subscript[2, 3]]
		ket[Subscript[{0,2,0}, 3]]
		ket[Subscript["020", 3]]
		-zm
		ket[(1/Sqrt[2])(zp+zm)]





kron[x, y, ...]
CircleTimes[x, y, ...]
	Returns the Kronecker product of x,y,... The arguments can be
	matrices, "ket", "unit", "state", etc., as long as the product is
	meaningful.

	This function in Mathematica can be called in infix notation
	using the operator "CircleTimes" by typing: "ESC" "c" "*"
	"ESC".  Note that this operator has a weaker precedence than the
	"Dot" product, which denoted with ".".

	Try:
		kron[zp, xp]
		kron[wh, cnot]
		kron[zm, maxmix[2]]
		kron[mm, mm]
		kron[mm, wh]





krondiv[v, w]
	"Kronecker division". krondiv returns a matrix y of dimension
	N/n x 1, such that v = kron[w,y], where v is a matrix of
	dimension N x 1, and w is matrix of dimension n x 1.

	The function krondiv only accepts Mathematica matrices, and no other
	types of data, such as "ket".

	Note that lines of a column vector can be created in Mathematica
	using the 2D notation: "CTRL-RETURN".

	Try:
		krondiv[{{4},{5},{8},{10},{12},{15}}, {{1},{2},{3}}]





kronexp[x, n]
	n-fold Kronecker product.

	Try:
		kronexp[wh, 3]
		kronexp[mm, 3]
		kronexp[zp, 3] == ket["000"]

	See also:
		kron, dotexp




lvProd[x, y]
CenterDot[x, y]
lvNorm[x]
	lvProd[x, y] returns the Liouville product of x and y.  The
	arguments may be of data type "unit" or "state".  The
	Liouville product of x and y is defined as the trace of the
	matrix product of dag[x] and y.

	This function may be entered in infix notation using the
	Mathematica operator "CenterDot", type "ESC" "." "ESC".  Note
	that this operator has a weaker precedence than the ordinary
	"Dot" product, and weaker also than the kronecker product
	"kron".

	lvNorm[x] returns the Liouville norm of x.  The argument may
	be of data type "unit" or "state".  The Liouville norm of x is
	defined as the square root of the Liouville product of x with
	itself.

	Try:
		lvProd[sigx, sigz]
		lvNorm[maxmix[2]]





maxmix[n]
	Returns the maximally mixed density matrix of dimension n.

	Try:
		maxmix[3]





mm
	Constant of type "supop" representing a 1-qubit measuring process in
	the canonical basis.

	Try:
		mm
		mm . xp
		mm . zp
		kron[mm, mm]
		mm . mm == mm
		wh . mm . wh





mmm
	Constant of type "sqo" representing a 1-qubit measuring process in
	the canonical basis.

	Try:
		mmm
		mmm . xp
		mmm . zp
		kron[mmm, id[]]
		mmm . mmm == mm

	See also:
		mm, sqo




randomUnit[]
	Returns a random unitary transformation of dimension 2.  The
	distribution of the outcome is based on a uniform random
	choice of the Euler angles in the Bloch-Poincaré sphere.

	More precisely, randomUnit[] is defined as follows:
		phase[t1] . rotz[t2] . roty[t3] . rotz[t4]
	where t1, t2, t3, and t4 are independent and identically distributed
	uniform random variables chosen between 0 and 2 Pi.

	Try:
		randomUnit[] . zp

	See also:
		phase, unit




phase[t]
rotx[t]
roty[t]
rotz[t]
	phase[t] is a global phase change with angle t applied to 1 qubit.

	rotx[t], roty[t] and rotz[t] are rotations around the axis
	corresponding to the function name in the Bloch-Poincaré sphere.

	Try:
		phase[t]
		rotx[t]
		roty[t]
		rotz[t]





schmidt[...]
	Data type representing a Schmidt decomposition of a pure state
	seen as a bipartite state.

	A well-defined "schmidt" contains a list of triplets {q, k1,
	k2}, where the q's are the Schmidt coefficients of the
	decomposition, the sum of the q^2 must be 1. The k1's (the
	k2's) are objects of type "ket", which form an orthonormal
	basis, the Schmidt basis, of Alice's (Bob's) sub-space.

	The expression schmidt[n1,n2,k], where k is a "ket" of dimension
	n1*n2 is converted so as to represent a Schmidt decomposition
	of k with n1 and n2 as the respective dimensions of the spaces
	of the two parties (Alice and Bob).  A fourth optional
	argument, of Mathematica type "pure function", may be passed.
	It is a simplification function that will be called at certain
	stages of the computation.  The call schmidt[n1, n2, k] is
	equivalent to schmidt[n1, n2, k, (Simplify[#])&].

	Try:
		s = schmidt[2,2,phip]
		FullForm[s]
		FullForm[s[[1]]]
		ket[s]





sqo[...]
	Data type representing a "selective quantum operation" (SQO).

	Mathematically, a SQO is defined as a family of square or
	rectangular matrices A_{i,j}, 1<=i<=m, 1<=j<=k_i, of dimension
	s x r, such that
		\sum A_{i,j}^\dagger A_{i,j}
	is equal to the r x r identity matrix. A SQO is a general
	quantum operation which includes, as special cases, unitary
	transformations, superoperators, POVMs (Positive Operator
	Valued Measure), trace-out's, or the effect of adding
	ancillae. When applied to a mixed state \rho, of arbitrary
	dimension r, a SQO returns with probability p_i the state
		\sigma_i = (1/p_i) B_i
	of dimension s, where
		B_i = \sum_{j} A_{i,j} \rho A_{i,j}^\dagger
		p_i = tr(B_i).

	It is very unlikely that you will have to build a "sqo"
	entirely from scratch, except possibly for the case where a
	measurement along non-orthogonal axes has to be made. In
	general, it is sufficient to combine the sqo's already defined
	in QuCalc with some unitary transformations to obtain a general
	quantum operation. To get acquainted with the details of a
	"sqo", refer to the examples given below.

	Try:
		mmm
		FullForm[mmm]
		q = kron[mmm, mm]
		FullForm[q]
		mmm . xp




state[...]
	Data type representing (in general) a mixed state.

	A well-defined "state" must contain a positive hermitian square
	matrix with trace equal to one.

	Note that in 2D notation, "CTRL-RETURN" can be used to create
	the lines of a matrix, whereas "CTRL-," is used to create the
	columns.

	An object "state" representing a pure state is not automatically
	converted into a "ket"; use "eigen" to force that conversion.

	Try:
		r = state[phip]
		FullForm[r]
		FullForm[r[[1]]]
		state[(1/2)(state[phip] + state[phim])]




supop[...]
	Data type representing a superoperator.

	A well-defined "supop" must contain a list of square matrices A_j
	such that
		\sum_j A_j^\dagger A_j
	is equal to the identity matrix. When applied to a mixed state \rho,
	a "supop" returns the mixed state
		\sum_{j} A_j \rho A_j^\dagger
	as long as the dimensions of the matrices are compatible.

	In 2D notation, "CTRL-RETURN" can be used to create the lines of a
	matrix, whereas "CTRL-," is used to create the columns.

	Try:
		mm
		FullForm[mm]
		mm . xp





swap[n, i, j]
swap[]
	Returns a unitary transformation acting on n qubits, and whose
	action is to swap qubits i and j.

	swap[] is equivalent to swap[2,1,2].

	Try:
		c = swap[4,1,3]
		c . ket["0110"] == ket["1100"]
		Power[c,2] == id[4]

	See also:
		circuit




ensQ[x]
ketQ[x]
sqoQ[x]
stateQ[x]
supopQ[x]
unitQ[x]
	Boolean functions testing the validity of x according to the type
	structure associated with the function name.

	Try:
		unitQ[wh]
		Simplify[unitQ[fourier[3]]]
		ketQ[ket[zp + zm]]




trout[nA, nB, nC]
	This functions returns a "sqo" data structure representing the
	operation of tracing out a Hilbert space of dimension nB in
	between 2 Hilbert spaces of dimension nA and nC.

	Try:
		trout[2, 2, 1] . phip
		trout[1, 2, 2] . phip
		trout[2, 4, 2] . ket["0110"] == state[ket["00"]]





unit[...]
	Data type corresponding to unitary transformations.

	A valid "unit" data is a square unitary matrix.

	Note that a matrix in 2D notation can be built using "CRTL-RETURN"
	to create lines and "CTRL-," to create columns.

	Try:
		FullForm[sigz]
		FullForm[sigz[[1]]]
		I wh
		unit[Exp[(I Pi)/4] wh]
		unit[(1/Sqrt[3])(sigx + sigy + sigz)]





vec[x]
unvec[v, n]
	This function transforms a matrix x into a vector. The columns of
	the matrix (from left to right) are concatenated in the vector in
	top-down order.

	unvec[v, n] undo the transformation by re-transforming a vector v
	into a matrix containing n lines.

	These functions are defined for Mathematica matrices; they cannot be
	applied to a "ket" or any other data types specific to QuCalc.

	In 2D notation "CTRL-RETURN" can be used to create lines of a
	matrix, whereas "CTRL-," is used to create the columns.

	Try:
		v = vec[{{1,2,3},{4,5,6},{7,8,9},{10,11,12}}]
		FullForm[v]
		unvec[v, 2]




Mathematica provides for entering mathematical expressions in "2D
notation".  This is handy for entering data into matrices. Type:
	"CTRL-RETURN" to create lines,
	"CTRL-," to create columns.
Boxes or \[Placeholder] appear to help filling the entries.

Noteworthy is the argument to QuCalc function "circuit" which is a
matrix and can thus be filled in this way.  In that context, if a box
is left empty, it will be interpreted as the trivial identity
operator.

The other 2D notation shortcuts used in QuCalc are:
	«CTRL-&» «_» : complex conjugate,
	«CTRL-&» «~» : negation of a bit string,
	«CTRL-^» «ESC» «d» «g» «ESC» : conjugate and transpose of a matrix,
	«CTRL-^» : to enter an exponent,
	«CTRL-_» : to enter a subscript.

See also:
	circuit, OverBar, OverTilde, Power, Subscript, SuperDagger




Subscript is the Mathematica function to define subscripts and
it is linked to the 2D notation shortcut "CTRL-_".

QuCalc overloads this function in a number of ways.





regSet[l]
regGet[]
	regSet[l] uses the elements of the list l to define the names
	of the quantum registers that will be used by regOper,
	regState, regTrout and regAnc.  The members of l can be
	identifiers, integers, character strings, etc., but they
	cannot be lists.  Each register holds 1 qubit and thus a
	2-dimensional Hilbert space.  Two distinct registers cannot
	have the same name.

	regGet[] returns the list of register names previously defined
	by the last call to regSet.

	Try:
		regSet[{Alice, Bob}]
		regGet[]
		regSet[{z,y,x,1,2,3}]
		regGet[]





regOper[o,l]
	The argument o is either a "unit", a "supop" or a "sqo", of
	square dimension, and l is a list of registers previously
	defined with a call to regSet.  The number of qubits upon
	which o is operating must be equal to the length of l.  The
	call regOper[o,l] returns o operating in the given registers.
	The identity operator is implicitly used on the registers not
	in l but defined with the last call to regSet.

	The calls Subscript[o, r1,r2,...] or Subscript[o, {r1,r2,...}] 
	are converted into regOper[o, {r1,r2,...}].  Therefore, the
	function can be entered by using Mathematica 2D notation
	"CTRL-_".

	Try:
		regSet[{a,b}]
		regOper[cnot, {a,b}]
		regOper[cnot, {b,a}]
		regSet[{a,z,b}]
		regOper[cnot, {a,b}]
		regOper[cnot, {b,a}]





regState[s,l]
	The argument s is either a "ket", a "state" or a "ens", and l
	is the list of registers previously defined with a call to
	regSet.  The list l must contain all the registers declared
	with regSet but they need not be in the same order.  The
	number of qubits in the state s must be equal to the number of
	registers.  The call regState[s,l] returns s within the
	registers given in l in that order.

	The calls
		kron[Subscript[s1, r1,r2,...], Subscript[s2, t1,t2,...]]
	or
		kron[Subscript[s1, {r1,r2,...}], Subscript[s2, {t1,t2,...}]]
	are converted into
		regState[kron[s1,s2], {r1,r2,...,t1,t2,...}].
	Therefore this function can be entered using Mathematica 2D
	notation with "CTRL-_" to define subscripts and with
	«ESC» «c» «*» «ESC» for the infix Kronecker product.  This
	syntax is handy if combined with the similar one for the
	function regOper, as illustrated below.

	In the following examples, you need to type "CTRL-_" wherever
	"_" is written, and type «ESC» «c» «*» «ESC» wherever "*" is
	written.  Try:
		regSet[{Alice,Bob}]
		wh_Alice . not_Bob . (zp_Alice * zm_Bob)
		wh_Alice . not_Bob . (zm_Bob * zp_Alice)
		not_Bob . wh_Alice . (zp_Alice * zm_Bob)
		not_Bob . wh_Alice . (zm_Bob * zp_Alice)





regTrout[l]
	The list l contains the names of some registers previously
	defined with a call to regSet.  The call regTrout[l] returns a
	"sqo" that represents the operation of tracing out the given
	registers with respect to the surrounding space defined with
	regSet.

	Try:
		regSet[{1,2,3,4}]
		regTrout[{3,1}].ket["0101"] == state[ket["11"]]





regAnc[l]
	The list l contains the names of some registers previously
	defined with a call to regSet.  The call regAnc[l] returns a
	"sqo" that represents the operation of adding an ancilla
	initialized to "ket[0]".  The ancillary registers are given by
	l and the resulting space is such as defined with regSet.

	Try:
		regSet[{1,2,3,4}]
		regAnc[{3,1}].ket["11"] == state[ket["0101"]]

