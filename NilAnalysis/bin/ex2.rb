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

#a = 10
#if 5 < 4 then
	#b = a;
#else
	#a=2;
#end 

A_v = 2
a = 1
b = 2
#c = a + (b < (a+b))
c = A_v.abs
a.abs.to_s