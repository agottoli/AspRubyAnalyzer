a=0; b=nil;
if guardia then
	a=1; b=1; c=1
else
a=2; b=2
end
a.to_s		#NonNil (sempre definita)
b.to_s		#NonNil (prima Nil, poi definita in entrambi i rami)
c.to_s		#MaybeNil (definita solo in un ramo)
