a = 1
b = 2
c = 3
d = 4
for i,j in [[a,b],[c,d],[1,2]] do
	a = i + j
	puts a
end

#for i,j in a do
	#puts i+j
#	puts a
#	puts j
#end 
#a.to_s		#NonNil (sempre definita)
#b.to_s		#MaybeNil (se la guardia fosse vuota il For non verrebbe eseguito)
