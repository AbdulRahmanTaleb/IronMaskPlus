#ORDER 7
#SHARES 8
#IN a b
#RANDOMS r01 r02 r03 r04 r05 r06 r07 r12 r13 r14 r15 r16 r17 r23 r24 r25 r26 r27 r34 r35 r36 r37 r45 r46 r47 r56 r57 r67 rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7
#OUT c

h0 = rr0 + rr1
h0 = h0 + a0

h1 = rr1 + rr2
h1 = h1 + a1

h2 = rr2 + rr3
h2 = h2 + a2

h3 = rr3 + rr4
h3 = h3 + a3

h4 = rr4 + rr5
h4 = h4 + a4

h5 = rr5 + rr6
h5 = h5 + a5

h6 = rr6 + rr7
h6 = h6 + a6

h7 = rr7 + rr0
h7 = h7 + a7


tmp = h0 * b1
r10 = r01 + tmp
tmp = h1 * b0
r10 = r10 + tmp

tmp = h0 * b2
r20 = r02 + tmp
tmp = h2 * b0
r20 = r20 + tmp

tmp = h0 * b3
r30 = r03 + tmp
tmp = h3 * b0
r30 = r30 + tmp

tmp = h0 * b4
r40 = r04 + tmp
tmp = h4 * b0
r40 = r40 + tmp

tmp = h0 * b5
r50 = r05 + tmp
tmp = h5 * b0
r50 = r50 + tmp

tmp = h0 * b6
r60 = r06 + tmp
tmp = h6 * b0
r60 = r60 + tmp

tmp = h0 * b7
r70 = r07 + tmp
tmp = h7 * b0
r70 = r70 + tmp

tmp = h1 * b2
r21 = r12 + tmp
tmp = h2 * b1
r21 = r21 + tmp

tmp = h1 * b3
r31 = r13 + tmp
tmp = h3 * b1
r31 = r31 + tmp

tmp = h1 * b4
r41 = r14 + tmp
tmp = h4 * b1
r41 = r41 + tmp

tmp = h1 * b5
r51 = r15 + tmp
tmp = h5 * b1
r51 = r51 + tmp

tmp = h1 * b6
r61 = r16 + tmp
tmp = h6 * b1
r61 = r61 + tmp

tmp = h1 * b7
r71 = r17 + tmp
tmp = h7 * b1
r71 = r71 + tmp

tmp = h2 * b3
r32 = r23 + tmp
tmp = h3 * b2
r32 = r32 + tmp

tmp = h2 * b4
r42 = r24 + tmp
tmp = h4 * b2
r42 = r42 + tmp

tmp = h2 * b5
r52 = r25 + tmp
tmp = h5 * b2
r52 = r52 + tmp

tmp = h2 * b6
r62 = r26 + tmp
tmp = h6 * b2
r62 = r62 + tmp

tmp = h2 * b7
r72 = r27 + tmp
tmp = h7 * b2
r72 = r72 + tmp

tmp = h3 * b4
r43 = r34 + tmp
tmp = h4 * b3
r43 = r43 + tmp

tmp = h3 * b5
r53 = r35 + tmp
tmp = h5 * b3
r53 = r53 + tmp

tmp = h3 * b6
r63 = r36 + tmp
tmp = h6 * b3
r63 = r63 + tmp

tmp = h3 * b7
r73 = r37 + tmp
tmp = h7 * b3
r73 = r73 + tmp

tmp = h4 * b5
r54 = r45 + tmp
tmp = h5 * b4
r54 = r54 + tmp

tmp = h4 * b6
r64 = r46 + tmp
tmp = h6 * b4
r64 = r64 + tmp

tmp = h4 * b7
r74 = r47 + tmp
tmp = h7 * b4
r74 = r74 + tmp

tmp = h5 * b6
r65 = r56 + tmp
tmp = h6 * b5
r65 = r65 + tmp

tmp = h5 * b7
r75 = r57 + tmp
tmp = h7 * b5
r75 = r75 + tmp

tmp = h6 * b7
r76 = r67 + tmp
tmp = h7 * b6
r76 = r76 + tmp

tmp = h0 * b0
c0 = tmp + r01
c0 = c0 + r02
c0 = c0 + r03
c0 = c0 + r04
c0 = c0 + r05
c0 = c0 + r06
c0 = c0 + r07

tmp = h1 * b1
c1 = tmp + r12
c1 = c1 + r13
c1 = c1 + r14
c1 = c1 + r15
c1 = c1 + r16
c1 = c1 + r17
c1 = c1 + r10

tmp = h2 * b2
c2 = tmp + r23
c2 = c2 + r24
c2 = c2 + r25
c2 = c2 + r26
c2 = c2 + r27
c2 = c2 + r20
c2 = c2 + r21

tmp = h3 * b3
c3 = tmp + r34
c3 = c3 + r35
c3 = c3 + r36
c3 = c3 + r37
c3 = c3 + r30
c3 = c3 + r31
c3 = c3 + r32

tmp = h4 * b4
c4 = tmp + r45
c4 = c4 + r46
c4 = c4 + r47
c4 = c4 + r40
c4 = c4 + r41
c4 = c4 + r42
c4 = c4 + r43

tmp = h5 * b5
c5 = tmp + r56
c5 = c5 + r57
c5 = c5 + r50
c5 = c5 + r51
c5 = c5 + r52
c5 = c5 + r53
c5 = c5 + r54

tmp = h6 * b6
c6 = tmp + r67
c6 = c6 + r60
c6 = c6 + r61
c6 = c6 + r62
c6 = c6 + r63
c6 = c6 + r64
c6 = c6 + r65

tmp = h7 * b7
c7 = tmp + r70
c7 = c7 + r71
c7 = c7 + r72
c7 = c7 + r73
c7 = c7 + r74
c7 = c7 + r75
c7 = c7 + r76
