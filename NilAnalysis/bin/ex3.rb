a=1
guardia = 12
while guardia < 10 do
	a.to_s		#MaybeNil (NonNil all'inizio, MaybeNil alla seconda iterazione)
	a=2
	a.to_s 		#NonNil
	a=nil
	b=3
end
a.to_s 			#MaybeNil
b.to_s 			#MaybeNil (il while potremmo non essere mai eseguito)
