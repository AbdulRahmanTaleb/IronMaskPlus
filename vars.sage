


P.<a0_0,a0_1,a0_2,a1_0,a1_1,a1_2,b0_0,b0_1,b0_2,b1_0,b1_1,b1_2,r0,r1>=BooleanPolynomialRing()


v =  (  (  (  (  ( a1_1  + 1  )  + 1  )  *  (  ( b1_1  + 1  )  + 1  )  *  (  ( a1_0  + 1  )  + 1  )  *  (  ( b1_0  + 1  )  + 1  )  + 1  )  *  (  (  ( a1_2  + 1  )  + 1  )  *  (  ( b1_2  + 1  )  + 1  )  *  (  (  (  ( a1_1  + 1  )  + 1  )  *  (  ( b1_1  + 1  )  + 1  )  + 1  )  *  (  (  ( a1_0  + 1  )  + 1  )  *  (  ( b1_0  + 1  )  + 1  )  + 1  )  + 1  )  + 1  )  + 1  )  +  (  (  ( r0  +  ( r1  +  (  ( a1_1  + 1  )  + 1  )  *  (  ( b0_1  + 1  )  + 1  )  )  )  *  ( r0  +  ( r1  +  (  ( a1_0  + 1  )  + 1  )  *  (  ( b0_0  + 1  )  + 1  )  )  )  + 1  )  *  (  ( r0  +  ( r1  +  (  ( a1_2  + 1  )  + 1  )  *  (  ( b0_2  + 1  )  + 1  )  )  )  *  (  (  ( r0  +  ( r1  +  (  ( a1_1  + 1  )  + 1  )  *  (  ( b0_1  + 1  )  + 1  )  )  )  + 1  )  *  (  ( r0  +  ( r1  +  (  ( a1_0  + 1  )  + 1  )  *  (  ( b0_0  + 1  )  + 1  )  )  )  + 1  )  + 1  )  + 1  )  + 1  )  ) 


print(v)

v1 = (  (  ( 0  + b0_0  )  + 1  )  *  (  ( r0  + b0_2  )  + 1  )  + 1  )  *  (  (  ( r0  + b0_2  )  *  ( 0  + b0_0  )  + 1  )  *  (  ( r0  + b0_1  )  + 1  )  + 1  ) 

v2 =  (  (  ( 0  + b0_0  )  + 1  )  *  (  ( r0  + b0_2  )  + 1  )  + 1  )  *  (  (  ( r0  + b0_2  )  *  ( 0  + b0_0  )  + 1  )  *  (  ( r0  + b0_1  )  + 1  )  + 1  ) 

v3 =  (  (  ( 0  + b0_0  )  + 1  )  *  (  ( r0  + b0_2  )  + 1  )  + 1  )  *  (  (  ( r0  + b0_2  )  *  ( 0  + b0_0  )  + 1  )  *  (  ( r0  + b0_1  )  + 1  )  + 1  ) 


print(v1)

print(v2)

print(v3)