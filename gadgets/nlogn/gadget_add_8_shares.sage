#SHARES 8
#IN a b
#RANDOMS r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 r32 r33 r34 r35 r36 r37 r38 r39 
#OUT d

j0 = a0 + r0
j4 = a4 + r0
j1 = a1 + r1
j5 = a5 + r1
j2 = a2 + r2
j6 = a6 + r2
j3 = a3 + r3
j7 = a7 + r3


j0 = j0 + r4
j2 = j2 + r4
j1 = j1 + r5
j3 = j3 + r5


k0 = j0 + r6
k1 = j1 + r6


k2 = j2 + r7
k3 = j3 + r7


k0 = k0 + r8
k2 = k2 + r8
k1 = k1 + r9
k3 = k3 + r9


j4 = j4 + r10
j6 = j6 + r10
j5 = j5 + r11
j7 = j7 + r11


k4 = j4 + r12
k5 = j5 + r12


k6 = j6 + r13
k7 = j7 + r13


k4 = k4 + r14
k6 = k6 + r14
k5 = k5 + r15
k7 = k7 + r15


e0 = k0 + r16
e4 = k4 + r16
e1 = k1 + r17
e5 = k5 + r17
e2 = k2 + r18
e6 = k6 + r18
e3 = k3 + r19
e7 = k7 + r19


j0 = b0 + r20
j4 = b4 + r20
j1 = b1 + r21
j5 = b5 + r21
j2 = b2 + r22
j6 = b6 + r22
j3 = b3 + r23
j7 = b7 + r23


j0 = j0 + r24
j2 = j2 + r24
j1 = j1 + r25
j3 = j3 + r25


k0 = j0 + r26
k1 = j1 + r26


k2 = j2 + r27
k3 = j3 + r27


k0 = k0 + r28
k2 = k2 + r28
k1 = k1 + r29
k3 = k3 + r29


j4 = j4 + r30
j6 = j6 + r30
j5 = j5 + r31
j7 = j7 + r31


k4 = j4 + r32
k5 = j5 + r32


k6 = j6 + r33
k7 = j7 + r33


k4 = k4 + r34
k6 = k6 + r34
k5 = k5 + r35
k7 = k7 + r35


f0 = k0 + r36
f4 = k4 + r36
f1 = k1 + r37
f5 = k5 + r37
f2 = k2 + r38
f6 = k6 + r38
f3 = k3 + r39
f7 = k7 + r39


d0 = e0 + f0
d1 = e1 + f1
d2 = e2 + f2
d3 = e3 + f3
d4 = e4 + f4
d5 = e5 + f5
d6 = e6 + f6
d7 = e7 + f7
