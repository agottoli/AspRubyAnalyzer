a=1
guard = 7
while guard < 10 do
	a.to_s		#MaybeNil (NonNil all'inizio, MaybeNil alla seconda iterazione)
	a= a + guard
	guard = guard + 1
end
a.to_s 			#MaybeNil
quard.to_s 			#MaybeNil (il while potremmo non essere mai eseguito)
