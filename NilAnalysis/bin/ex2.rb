#a=0; b=nil;
#c = 3;
#d = a+c;
#if guardia then
#	a=1; b=1; c=1
#else
#a=2; b=2
#end
#a.to_s		#NonNil (sempre definita)
#b.to_s		#NonNil (prima Nil, poi definita in entrambi i rami)
#c.to_s		#MaybeNil (definita solo in un ramo)

#a.to_s

a = 10
b=3
if (5 < 4) & (3 > 1) then
	b = a;
#else
#	a=2;
end 

A_v = 2
a = 1
b = 2
c = a + (b < (a+b))
#x,y,z=A_v,a,b
#[a,b].minmax 
#a=0
#c = A_v.abs
#a.abs.to_s
c = a + b

c = Math.max(10, 5)