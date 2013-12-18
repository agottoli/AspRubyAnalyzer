a=0
for i,j in [[1,2],[3,4],[5,6]] do
	#puts i+j
	a=1
	b=2
end
a.to_s		#NonNil (sempre definita)
b.to_s		#MaybeNil (se la guardia fosse vuota il For non verrebbe eseguito)
