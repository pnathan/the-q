[tool-version] Z3 4.12.5
[mk-app] #1 true
[mk-app] #2 false
[mk-app] #1 true
[mk-app] #2 false
[mk-app] #3 pi
[mk-app] #4 euler
[mk-var] datatype#0 0
[mk-var] datatype#1 1
[mk-app] datatype#2 insert datatype#0 datatype#1
[mk-app] datatype#3 pattern datatype#2
[mk-app] datatype#4 head datatype#2
[mk-app] datatype#5 = datatype#0 datatype#4
[mk-quant] datatype#6 constructor_accessor_axiom 2 datatype#3 datatype#5
[attach-var-names] datatype#6 (;k!0) (;List)
[mk-app] datatype#7 tail datatype#2
[mk-app] datatype#8 = datatype#1 datatype#7
[mk-quant] datatype#9 constructor_accessor_axiom 2 datatype#3 datatype#8
[attach-var-names] datatype#9 (;k!0) (;List)
[mk-app] #5 bv
[attach-meaning] #5 bv #b1
[mk-app] #6 bv
[attach-meaning] #6 bv #b0
[attach-meaning] #5 bv #b1
[attach-meaning] #6 bv #b0
[attach-meaning] #6 bv #b0
[mk-var] #7 0
[mk-var] #8 1
[mk-var] #9 2
[mk-var] #10 3
[mk-var] #11 4
[mk-var] #12 5
[mk-var] #13 6
[mk-var] #14 7
[mk-var] #15 8
[mk-var] #16 9
[mk-var] #17 10
[mk-var] #18 11
[mk-var] #19 12
[mk-var] #20 13
[mk-var] #21 14
[mk-app] #22 + #15 #13
[attach-enode] #1 0
[attach-enode] #2 0
[mk-app] #23 fuel_defaults
[mk-var] #24 0
[mk-app] #25 fuel_bool #24
[mk-app] #26 fuel_bool_default #24
[mk-app] #27 = #25 #26
[mk-app] #28 pattern #25
[mk-quant] #29 prelude_fuel_defaults 1 #28 #27
[attach-var-names] #29 (|id| ; |FuelId|)
[mk-app] #30 => #23 #29
[mk-app] #31 not #23
[mk-app] #32 or #31 #29
[inst-discovered] theory-solving 0 basic# ; #30
[mk-app] #33 = #30 #32
[instance] 0 #33
[attach-enode] #33 0
[end-of-instance]
[mk-var] #33 1
[mk-var] #34 0
[mk-app] #35 mut_ref_update_current% #33 #34
[mk-app] #36 mut_ref_current% #35
[mk-app] #37 = #36 #34
[mk-app] #38 pattern #35
[mk-quant] #39 prelude_mut_ref_update_current_current 2 #38 #37
[attach-var-names] #39 (|arg| ; |Poly|) (|m| ; |Poly|)
[mk-app] #40 mut_ref_future% #35
[mk-app] #41 mut_ref_future% #33
[mk-app] #42 = #40 #41
[mk-quant] #43 prelude_mut_ref_update_current_future 2 #38 #42
[attach-var-names] #43 (|arg| ; |Poly|) (|m| ; |Poly|)
[mk-var] #44 2
[mk-var] #45 1
[mk-var] #46 0
[mk-app] #47 MUTREF #45 #46
[mk-app] #48 has_type #44 #47
[mk-app] #49 mut_ref_current% #44
[mk-app] #50 has_type #49 #46
[mk-app] #51 => #48 #50
[mk-app] #52 pattern #48 #49
[mk-quant] #53 prelude_mut_ref_current_has_type 3 #52 #51
[attach-var-names] #53 (|t| ; |Type|) (|d| ; |Dcr|) (|m| ; |Poly|)
[mk-app] #54 not #48
[mk-app] #55 or #54 #50
[inst-discovered] theory-solving 0 basic# ; #51
[mk-app] #56 = #51 #55
[instance] 0 #56
[attach-enode] #56 0
[end-of-instance]
[mk-quant] #56 prelude_mut_ref_current_has_type 3 #52 #55
[attach-var-names] #56 (|t| ; |Type|) (|d| ; |Dcr|) (|m| ; |Poly|)
[mk-app] #57 mut_ref_future% #44
[mk-app] #58 has_type #57 #46
[mk-app] #59 => #48 #58
[mk-app] #60 pattern #48 #57
[mk-quant] #61 prelude_mut_ref_current_has_type 3 #60 #59
[attach-var-names] #61 (|t| ; |Type|) (|d| ; |Dcr|) (|m| ; |Poly|)
[mk-app] #62 or #54 #58
[inst-discovered] theory-solving 0 basic# ; #59
[mk-app] #63 = #59 #62
[instance] 0 #63
[attach-enode] #63 0
[end-of-instance]
[mk-quant] #63 prelude_mut_ref_current_has_type 3 #60 #62
[attach-var-names] #63 (|t| ; |Type|) (|d| ; |Dcr|) (|m| ; |Poly|)
[mk-var] #64 3
[mk-var] #65 2
[mk-var] #66 1
[mk-app] #67 MUTREF #65 #66
[mk-app] #68 has_type #64 #67
[mk-app] #69 has_type #34 #66
[mk-app] #70 and #68 #69
[mk-app] #71 mut_ref_update_current% #64 #34
[mk-app] #72 has_type #71 #67
[mk-app] #73 => #70 #72
[mk-app] #74 pattern #68 #71
[mk-quant] #75 prelude_mut_ref_update_has_type 4 #74 #73
[attach-var-names] #75 (|arg| ; |Poly|) (|t| ; |Type|) (|d| ; |Dcr|) (|m| ; |Poly|)
[mk-app] #76 not #70
[mk-app] #77 or #76 #72
[inst-discovered] theory-solving 0 basic# ; #73
[mk-app] #78 = #73 #77
[instance] 0 #78
[attach-enode] #78 0
[end-of-instance]
[mk-quant] #78 prelude_mut_ref_update_has_type 4 #74 #77
[attach-var-names] #78 (|arg| ; |Poly|) (|t| ; |Type|) (|d| ; |Dcr|) (|m| ; |Poly|)
[mk-var] #79 0
[mk-app] #80 sized #79
[mk-app] #81 DST #79
[mk-app] #82 sized #81
[mk-app] #83 => #80 #82
[mk-app] #84 pattern #82
[mk-quant] #85 prelude_sized_decorate_struct_inherit 1 #84 #83
[attach-var-names] #85 (|d| ; |Dcr|)
[mk-app] #86 not #80
[mk-app] #87 or #86 #82
[inst-discovered] theory-solving 0 basic# ; #83
[mk-app] #88 = #83 #87
[instance] 0 #88
[attach-enode] #88 0
[end-of-instance]
[mk-quant] #88 prelude_sized_decorate_struct_inherit 1 #84 #87
[attach-var-names] #88 (|d| ; |Dcr|)
[mk-app] #89 REF #79
[mk-app] #90 sized #89
[mk-app] #91 pattern #90
[mk-quant] #92 prelude_sized_decorate_ref 1 #91 #90
[attach-var-names] #92 (|d| ; |Dcr|)
[mk-app] #93 BOX #65 #66 #79
[mk-app] #94 sized #93
[mk-app] #95 pattern #94
[mk-quant] #96 prelude_sized_decorate_box 3 #95 #94
[attach-var-names] #96 (|d2| ; |Dcr|) (|t| ; |Type|) (|d| ; |Dcr|)
[mk-app] #97 RC #65 #66 #79
[mk-app] #98 sized #97
[mk-app] #99 pattern #98
[mk-quant] #100 prelude_sized_decorate_rc 3 #99 #98
[attach-var-names] #100 (|d2| ; |Dcr|) (|t| ; |Type|) (|d| ; |Dcr|)
[mk-app] #101 ARC #65 #66 #79
[mk-app] #102 sized #101
[mk-app] #103 pattern #102
[mk-quant] #104 prelude_sized_decorate_arc 3 #103 #102
[attach-var-names] #104 (|d2| ; |Dcr|) (|t| ; |Type|) (|d| ; |Dcr|)
[mk-app] #105 GHOST #79
[mk-app] #106 sized #105
[mk-app] #107 pattern #106
[mk-quant] #108 prelude_sized_decorate_ghost 1 #107 #106
[attach-var-names] #108 (|d| ; |Dcr|)
[mk-app] #109 TRACKED #79
[mk-app] #110 sized #109
[mk-app] #111 pattern #110
[mk-quant] #112 prelude_sized_decorate_tracked 1 #111 #110
[attach-var-names] #112 (|d| ; |Dcr|)
[mk-app] #113 NEVER #79
[mk-app] #114 sized #113
[mk-app] #115 pattern #114
[mk-quant] #116 prelude_sized_decorate_never 1 #115 #114
[attach-var-names] #116 (|d| ; |Dcr|)
[mk-app] #117 CONST_PTR #79
[mk-app] #118 sized #117
[mk-app] #119 pattern #118
[mk-quant] #120 prelude_sized_decorate_const_ptr 1 #119 #118
[attach-var-names] #120 (|d| ; |Dcr|)
[mk-app] #121 $
[mk-app] #122 sized #121
[mk-var] #123 0
[mk-app] #124 CONST_INT #123
[mk-app] #125 const_int #124
[mk-app] #126 = #123 #125
[mk-app] #127 pattern #124
[mk-quant] #128 prelude_type_id_const_int 1 #127 #126
[attach-var-names] #128 (|i| ; |Int|)
[mk-var] #129 0
[mk-app] #130 CONST_BOOL #129
[mk-app] #131 const_bool #130
[mk-app] #132 = #129 #131
[mk-app] #133 pattern #130
[mk-quant] #134 prelude_type_id_const_bool 1 #133 #132
[attach-var-names] #134 (|b| ; |Bool|)
[mk-app] #135 B #129
[mk-app] #136 BOOL
[mk-app] #137 has_type #135 #136
[mk-app] #138 pattern #137
[mk-quant] #139 prelude_has_type_bool 1 #138 #137
[attach-var-names] #139 (|b| ; |Bool|)
[mk-app] #140 R #7
[mk-app] #141 REAL
[mk-app] #142 has_type #140 #141
[mk-app] #143 pattern #142
[mk-quant] #144 prelude_has_type_real 1 #143 #142
[attach-var-names] #144 (|r| ; |Real|)
[mk-app] #145 as_type #33 #46
[mk-app] #146 has_type #145 #46
[mk-app] #147 has_type #33 #46
[mk-app] #148 = #33 #145
[mk-app] #149 => #147 #148
[mk-app] #150 and #146 #149
[mk-app] #151 pattern #145
[mk-quant] #152 prelude_as_type 2 #151 #150
[attach-var-names] #152 (|t| ; |Type|) (|x| ; |Poly|)
[mk-app] #153 not #147
[mk-app] #154 or #153 #148
[inst-discovered] theory-solving 0 basic# ; #149
[mk-app] #155 = #149 #154
[instance] 0 #155
[attach-enode] #155 0
[end-of-instance]
[mk-app] #155 and #146 #154
[mk-quant] #156 prelude_as_type 2 #151 #155
[attach-var-names] #156 (|t| ; |Type|) (|x| ; |Poly|)
[mk-var] #157 0
[mk-app] #158 mk_fun #157
[mk-app] #159 = #158 #157
[mk-app] #160 pattern #158
[mk-quant] #161 prelude_mk_fun 1 #160 #159
[attach-var-names] #161 (|x| ; |%%Function%%|)
[mk-app] #162 %B #135
[mk-app] #163 = #129 #162
[mk-app] #164 pattern #135
[mk-quant] #165 prelude_unbox_box_bool 1 #164 #163
[attach-var-names] #165 (|x| ; |Bool|)
[mk-app] #166 I #123
[mk-app] #167 %I #166
[mk-app] #168 = #123 #167
[mk-app] #169 pattern #166
[mk-quant] #170 prelude_unbox_box_int 1 #169 #168
[attach-var-names] #170 (|x| ; |Int|)
[mk-app] #171 %R #140
[mk-app] #172 = #7 #171
[mk-app] #173 pattern #140
[mk-quant] #174 prelude_unbox_box_real 1 #173 #172
[attach-var-names] #174 (|x| ; |Real|)
[mk-app] #175 has_type #34 #136
[mk-app] #176 %B #34
[mk-app] #177 B #176
[mk-app] #178 = #34 #177
[mk-app] #179 => #175 #178
[mk-app] #180 pattern #175
[mk-quant] #181 prelude_box_unbox_bool 1 #180 #179
[attach-var-names] #181 (|x| ; |Poly|)
[mk-app] #182 not #175
[mk-app] #183 or #182 #178
[inst-discovered] theory-solving 0 basic# ; #179
[mk-app] #184 = #179 #183
[instance] 0 #184
[attach-enode] #184 0
[end-of-instance]
[mk-quant] #184 prelude_box_unbox_bool 1 #180 #183
[attach-var-names] #184 (|x| ; |Poly|)
[mk-app] #185 INT
[mk-app] #186 has_type #34 #185
[mk-app] #187 %I #34
[mk-app] #188 I #187
[mk-app] #189 = #34 #188
[mk-app] #190 => #186 #189
[mk-app] #191 pattern #186
[mk-quant] #192 prelude_box_unbox_int 1 #191 #190
[attach-var-names] #192 (|x| ; |Poly|)
[mk-app] #193 not #186
[mk-app] #194 or #193 #189
[inst-discovered] theory-solving 0 basic# ; #190
[mk-app] #195 = #190 #194
[instance] 0 #195
[attach-enode] #195 0
[end-of-instance]
[mk-quant] #195 prelude_box_unbox_int 1 #191 #194
[attach-var-names] #195 (|x| ; |Poly|)
[mk-app] #196 NAT
[mk-app] #197 has_type #34 #196
[mk-app] #198 => #197 #189
[mk-app] #199 pattern #197
[mk-quant] #200 prelude_box_unbox_nat 1 #199 #198
[attach-var-names] #200 (|x| ; |Poly|)
[mk-app] #201 not #197
[mk-app] #202 or #201 #189
[inst-discovered] theory-solving 0 basic# ; #198
[mk-app] #203 = #198 #202
[instance] 0 #203
[attach-enode] #203 0
[end-of-instance]
[mk-quant] #203 prelude_box_unbox_nat 1 #199 #202
[attach-var-names] #203 (|x| ; |Poly|)
[mk-app] #204 USIZE
[mk-app] #205 has_type #34 #204
[mk-app] #206 => #205 #189
[mk-app] #207 pattern #205
[mk-quant] #208 prelude_box_unbox_usize 1 #207 #206
[attach-var-names] #208 (|x| ; |Poly|)
[mk-app] #209 not #205
[mk-app] #210 or #209 #189
[inst-discovered] theory-solving 0 basic# ; #206
[mk-app] #211 = #206 #210
[instance] 0 #211
[attach-enode] #211 0
[end-of-instance]
[mk-quant] #211 prelude_box_unbox_usize 1 #207 #210
[attach-var-names] #211 (|x| ; |Poly|)
[mk-app] #212 ISIZE
[mk-app] #213 has_type #34 #212
[mk-app] #214 => #213 #189
[mk-app] #215 pattern #213
[mk-quant] #216 prelude_box_unbox_isize 1 #215 #214
[attach-var-names] #216 (|x| ; |Poly|)
[mk-app] #217 not #213
[mk-app] #218 or #217 #189
[inst-discovered] theory-solving 0 basic# ; #214
[mk-app] #219 = #214 #218
[instance] 0 #219
[attach-enode] #219 0
[end-of-instance]
[mk-quant] #219 prelude_box_unbox_isize 1 #215 #218
[attach-var-names] #219 (|x| ; |Poly|)
[mk-var] #220 1
[mk-app] #221 UINT #220
[mk-app] #222 has_type #34 #221
[mk-app] #223 => #222 #189
[mk-app] #224 pattern #222
[mk-quant] #225 prelude_box_unbox_uint 2 #224 #223
[attach-var-names] #225 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #226 not #222
[mk-app] #227 or #226 #189
[inst-discovered] theory-solving 0 basic# ; #223
[mk-app] #228 = #223 #227
[instance] 0 #228
[attach-enode] #228 0
[end-of-instance]
[mk-quant] #228 prelude_box_unbox_uint 2 #224 #227
[attach-var-names] #228 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #229 SINT #220
[mk-app] #230 has_type #34 #229
[mk-app] #231 => #230 #189
[mk-app] #232 pattern #230
[mk-quant] #233 prelude_box_unbox_sint 2 #232 #231
[attach-var-names] #233 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #234 not #230
[mk-app] #235 or #234 #189
[inst-discovered] theory-solving 0 basic# ; #231
[mk-app] #236 = #231 #235
[instance] 0 #236
[attach-enode] #236 0
[end-of-instance]
[mk-quant] #236 prelude_box_unbox_sint 2 #232 #235
[attach-var-names] #236 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #237 FLOAT #220
[mk-app] #238 has_type #34 #237
[mk-app] #239 => #238 #189
[mk-app] #240 pattern #238
[mk-quant] #241 prelude_box_unbox_sint 2 #240 #239
[attach-var-names] #241 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #242 not #238
[mk-app] #243 or #242 #189
[inst-discovered] theory-solving 0 basic# ; #239
[mk-app] #244 = #239 #243
[instance] 0 #244
[attach-enode] #244 0
[end-of-instance]
[mk-quant] #244 prelude_box_unbox_sint 2 #240 #243
[attach-var-names] #244 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #245 CHAR
[mk-app] #246 has_type #34 #245
[mk-app] #247 => #246 #189
[mk-app] #248 pattern #246
[mk-quant] #249 prelude_box_unbox_char 1 #248 #247
[attach-var-names] #249 (|x| ; |Poly|)
[mk-app] #250 not #246
[mk-app] #251 or #250 #189
[inst-discovered] theory-solving 0 basic# ; #247
[mk-app] #252 = #247 #251
[instance] 0 #252
[attach-enode] #252 0
[end-of-instance]
[mk-quant] #252 prelude_box_unbox_char 1 #248 #251
[attach-var-names] #252 (|x| ; |Poly|)
[mk-app] #253 has_type #34 #141
[mk-app] #254 %R #34
[mk-app] #255 R #254
[mk-app] #256 = #34 #255
[mk-app] #257 => #253 #256
[mk-app] #258 pattern #253
[mk-quant] #259 prelude_box_unbox_real 1 #258 #257
[attach-var-names] #259 (|x| ; |Poly|)
[mk-app] #260 not #253
[mk-app] #261 or #260 #256
[inst-discovered] theory-solving 0 basic# ; #257
[mk-app] #262 = #257 #261
[instance] 0 #262
[attach-enode] #262 0
[end-of-instance]
[mk-quant] #262 prelude_box_unbox_real 1 #258 #261
[attach-var-names] #262 (|x| ; |Poly|)
[mk-var] #263 3
[mk-var] #264 2
[mk-app] #265 = #33 #34
[mk-app] #266 ext_eq #263 #264 #33 #34
[mk-app] #267 = #265 #266
[mk-app] #268 pattern #266
[mk-quant] #269 prelude_ext_eq 4 #268 #267
[attach-var-names] #269 (|y| ; |Poly|) (|x| ; |Poly|) (|t| ; |Type|) (|deep| ; |Bool|)
[mk-app] #270 SZ
[mk-app] #271 Int
[attach-meaning] #271 arith 32
[mk-app] #272 = #270 #271
[mk-app] #273 Int
[attach-meaning] #273 arith 64
[mk-app] #274 = #270 #273
[mk-app] #275 or #272 #274
[mk-app] #276 Int
[attach-meaning] #276 arith 8
[mk-app] #277 uHi #276
[mk-app] #278 Int
[attach-meaning] #278 arith 256
[mk-app] #279 = #277 #278
[mk-app] #280 Int
[attach-meaning] #280 arith 16
[mk-app] #281 uHi #280
[mk-app] #282 Int
[attach-meaning] #282 arith 65536
[mk-app] #283 = #281 #282
[attach-meaning] #271 arith 32
[mk-app] #284 uHi #271
[mk-app] #285 Int
[attach-meaning] #285 arith 4294967296
[mk-app] #286 = #284 #285
[attach-meaning] #273 arith 64
[mk-app] #287 uHi #273
[mk-app] #288 Int
[attach-meaning] #288 arith 18446744073709551616
[mk-app] #289 = #287 #288
[mk-app] #290 Int
[attach-meaning] #290 arith 128
[mk-app] #291 uHi #290
[mk-app] #292 Int
[attach-meaning] #292 arith 1
[mk-app] #293 Int
[attach-meaning] #293 arith 340282366920938463463374607431768211455
[mk-app] #294 + #292 #293
[mk-app] #295 = #291 #294
[mk-app] #296 Int
[attach-meaning] #296 arith 340282366920938463463374607431768211456
[inst-discovered] theory-solving 0 arith# ; #294
[mk-app] #297 = #294 #296
[instance] 0 #297
[attach-enode] #297 0
[end-of-instance]
[mk-app] #297 = #291 #296
[mk-app] #298 iLo #276
[attach-meaning] #290 arith 128
[mk-app] #299 - #290
[mk-app] #300 = #298 #299
[mk-app] #301 Int
[attach-meaning] #301 arith (- 128)
[inst-discovered] theory-solving 0 arith# ; #299
[mk-app] #302 = #299 #301
[instance] 0 #302
[attach-enode] #302 0
[end-of-instance]
[mk-app] #302 = #298 #301
[attach-meaning] #280 arith 16
[mk-app] #303 iLo #280
[mk-app] #304 Int
[attach-meaning] #304 arith 32768
[mk-app] #305 - #304
[mk-app] #306 = #303 #305
[mk-app] #307 Int
[attach-meaning] #307 arith (- 32768)
[inst-discovered] theory-solving 0 arith# ; #305
[mk-app] #308 = #305 #307
[instance] 0 #308
[attach-enode] #308 0
[end-of-instance]
[mk-app] #308 = #303 #307
[attach-meaning] #271 arith 32
[mk-app] #309 iLo #271
[mk-app] #310 Int
[attach-meaning] #310 arith 2147483648
[mk-app] #311 - #310
[mk-app] #312 = #309 #311
[mk-app] #313 Int
[attach-meaning] #313 arith (- 2147483648)
[inst-discovered] theory-solving 0 arith# ; #311
[mk-app] #314 = #311 #313
[instance] 0 #314
[attach-enode] #314 0
[end-of-instance]
[mk-app] #314 = #309 #313
[attach-meaning] #273 arith 64
[mk-app] #315 iLo #273
[mk-app] #316 Int
[attach-meaning] #316 arith 9223372036854775808
[mk-app] #317 - #316
[mk-app] #318 = #315 #317
[mk-app] #319 Int
[attach-meaning] #319 arith (- 9223372036854775808)
[inst-discovered] theory-solving 0 arith# ; #317
[mk-app] #320 = #317 #319
[instance] 0 #320
[attach-enode] #320 0
[end-of-instance]
[mk-app] #320 = #315 #319
[attach-meaning] #290 arith 128
[mk-app] #321 iLo #290
[mk-app] #322 Int
[attach-meaning] #322 arith 170141183460469231731687303715884105728
[mk-app] #323 - #322
[mk-app] #324 = #321 #323
[mk-app] #325 Int
[attach-meaning] #325 arith (- 170141183460469231731687303715884105728)
[inst-discovered] theory-solving 0 arith# ; #323
[mk-app] #326 = #323 #325
[instance] 0 #326
[attach-enode] #326 0
[end-of-instance]
[mk-app] #326 = #321 #325
[mk-app] #327 iHi #276
[attach-meaning] #290 arith 128
[mk-app] #328 = #327 #290
[attach-meaning] #280 arith 16
[mk-app] #329 iHi #280
[attach-meaning] #304 arith 32768
[mk-app] #330 = #329 #304
[attach-meaning] #271 arith 32
[mk-app] #331 iHi #271
[attach-meaning] #310 arith 2147483648
[mk-app] #332 = #331 #310
[attach-meaning] #273 arith 64
[mk-app] #333 iHi #273
[attach-meaning] #316 arith 9223372036854775808
[mk-app] #334 = #333 #316
[attach-meaning] #290 arith 128
[mk-app] #335 iHi #290
[attach-meaning] #322 arith 170141183460469231731687303715884105728
[mk-app] #336 = #335 #322
[mk-app] #337 Int
[attach-meaning] #337 arith 0
[mk-app] #338 nClip #123
[mk-app] #339 <= #337 #338
[mk-app] #340 <= #337 #123
[mk-app] #341 = #123 #338
[mk-app] #342 => #340 #341
[mk-app] #343 and #339 #342
[mk-app] #344 pattern #338
[mk-quant] #345 prelude_nat_clip 1 #344 #343
[attach-var-names] #345 (|i| ; |Int|)
[mk-app] #346 Int
[attach-meaning] #346 arith (- 1)
[mk-app] #347 * #346 #338
[mk-app] #348 >= #338 #337
[inst-discovered] theory-solving 0 arith# ; #339
[mk-app] #346 = #339 #348
[instance] 0 #346
[attach-enode] #346 0
[end-of-instance]
[mk-app] #346 Int
[attach-meaning] #346 arith (- 1)
[mk-app] #347 * #346 #123
[mk-app] #349 >= #123 #337
[inst-discovered] theory-solving 0 arith# ; #340
[mk-app] #346 = #340 #349
[instance] 0 #346
[attach-enode] #346 0
[end-of-instance]
[mk-app] #346 not #349
[mk-app] #347 or #346 #341
[mk-app] #350 => #349 #341
[inst-discovered] theory-solving 0 basic# ; #350
[mk-app] #351 = #350 #347
[instance] 0 #351
[attach-enode] #351 0
[end-of-instance]
[mk-app] #350 and #348 #347
[mk-quant] #351 prelude_nat_clip 1 #344 #350
[attach-var-names] #351 (|i| ; |Int|)
[mk-app] #352 uClip #220 #123
[mk-app] #353 <= #337 #352
[mk-app] #354 uHi #220
[mk-app] #355 < #352 #354
[mk-app] #356 < #123 #354
[mk-app] #357 and #340 #356
[mk-app] #358 = #123 #352
[mk-app] #359 => #357 #358
[mk-app] #360 and #353 #355 #359
[mk-app] #361 pattern #352
[mk-quant] #362 prelude_u_clip 2 #361 #360
[attach-var-names] #362 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #363 Int
[attach-meaning] #363 arith (- 1)
[mk-app] #364 * #363 #352
[mk-app] #365 >= #352 #337
[inst-discovered] theory-solving 0 arith# ; #353
[mk-app] #363 = #353 #365
[instance] 0 #363
[attach-enode] #363 0
[end-of-instance]
[mk-app] #363 <= #354 #352
[mk-app] #364 not #363
[inst-discovered] theory-solving 0 arith# ; #355
[mk-app] #366 = #355 #364
[instance] 0 #366
[attach-enode] #366 0
[end-of-instance]
[mk-app] #366 Int
[attach-meaning] #366 arith (- 1)
[mk-app] #367 * #366 #352
[mk-app] #368 + #367 #354
[attach-meaning] #366 arith (- 1)
[mk-app] #369 * #366 #354
[mk-app] #370 + #352 #369
[mk-app] #367 >= #370 #337
[inst-discovered] theory-solving 0 arith# ; #363
[mk-app] #368 = #363 #367
[instance] 0 #368
[attach-enode] #368 0
[end-of-instance]
[mk-app] #368 not #367
[attach-meaning] #366 arith (- 1)
[mk-app] #371 * #366 #123
[inst-discovered] theory-solving 0 arith# ; #340
[mk-app] #371 = #340 #349
[instance] 0 #371
[attach-enode] #371 0
[end-of-instance]
[mk-app] #371 <= #354 #123
[mk-app] #372 not #371
[inst-discovered] theory-solving 0 arith# ; #356
[mk-app] #373 = #356 #372
[instance] 0 #373
[attach-enode] #373 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #373 * #366 #123
[mk-app] #374 + #373 #354
[attach-meaning] #366 arith (- 1)
[mk-app] #375 + #123 #369
[mk-app] #373 >= #375 #337
[inst-discovered] theory-solving 0 arith# ; #371
[mk-app] #374 = #371 #373
[instance] 0 #374
[attach-enode] #374 0
[end-of-instance]
[mk-app] #374 not #373
[mk-app] #376 and #349 #374
[mk-app] #377 not #376
[mk-app] #378 or #377 #358
[mk-app] #379 => #376 #358
[inst-discovered] theory-solving 0 basic# ; #379
[mk-app] #380 = #379 #378
[instance] 0 #380
[attach-enode] #380 0
[end-of-instance]
[mk-app] #379 and #365 #368 #378
[mk-quant] #380 prelude_u_clip 2 #361 #379
[attach-var-names] #380 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #363 iLo #220
[mk-app] #364 iClip #220 #123
[mk-app] #371 <= #363 #364
[mk-app] #372 iHi #220
[mk-app] #381 < #364 #372
[mk-app] #382 <= #363 #123
[mk-app] #383 < #123 #372
[mk-app] #384 and #382 #383
[mk-app] #385 = #123 #364
[mk-app] #386 => #384 #385
[mk-app] #387 and #371 #381 #386
[mk-app] #388 pattern #364
[mk-quant] #389 prelude_i_clip 2 #388 #387
[attach-var-names] #389 (|i| ; |Int|) (|bits| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #390 * #366 #364
[mk-app] #391 + #363 #390
[mk-app] #392 <= #391 #337
[inst-discovered] theory-solving 0 arith# ; #371
[mk-app] #393 = #371 #392
[instance] 0 #393
[attach-enode] #393 0
[end-of-instance]
[mk-app] #393 <= #372 #364
[mk-app] #394 not #393
[inst-discovered] theory-solving 0 arith# ; #381
[mk-app] #395 = #381 #394
[instance] 0 #395
[attach-enode] #395 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #395 + #390 #372
[attach-meaning] #366 arith (- 1)
[mk-app] #396 * #366 #372
[mk-app] #397 + #364 #396
[mk-app] #395 >= #397 #337
[inst-discovered] theory-solving 0 arith# ; #393
[mk-app] #398 = #393 #395
[instance] 0 #398
[attach-enode] #398 0
[end-of-instance]
[mk-app] #398 not #395
[attach-meaning] #366 arith (- 1)
[mk-app] #399 * #366 #123
[mk-app] #400 + #399 #363
[attach-meaning] #366 arith (- 1)
[mk-app] #401 * #366 #363
[mk-app] #402 + #123 #401
[mk-app] #399 >= #402 #337
[inst-discovered] theory-solving 0 arith# ; #382
[mk-app] #400 = #382 #399
[instance] 0 #400
[attach-enode] #400 0
[end-of-instance]
[mk-app] #400 <= #372 #123
[mk-app] #403 not #400
[inst-discovered] theory-solving 0 arith# ; #383
[mk-app] #404 = #383 #403
[instance] 0 #404
[attach-enode] #404 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #404 * #366 #123
[mk-app] #405 + #404 #372
[attach-meaning] #366 arith (- 1)
[mk-app] #406 + #123 #396
[mk-app] #404 >= #406 #337
[inst-discovered] theory-solving 0 arith# ; #400
[mk-app] #405 = #400 #404
[instance] 0 #405
[attach-enode] #405 0
[end-of-instance]
[mk-app] #405 not #404
[mk-app] #407 and #399 #405
[mk-app] #408 not #407
[mk-app] #409 or #408 #385
[mk-app] #410 => #407 #385
[inst-discovered] theory-solving 0 basic# ; #410
[mk-app] #411 = #410 #409
[instance] 0 #411
[attach-enode] #411 0
[end-of-instance]
[mk-app] #410 and #392 #398 #409
[mk-quant] #411 prelude_i_clip 2 #388 #410
[attach-var-names] #411 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #400 charClip #123
[mk-app] #403 <= #337 #400
[mk-app] #393 Int
[attach-meaning] #393 arith 55295
[mk-app] #394 <= #400 #393
[mk-app] #412 and #403 #394
[mk-app] #413 Int
[attach-meaning] #413 arith 57344
[mk-app] #414 <= #413 #400
[mk-app] #415 Int
[attach-meaning] #415 arith 1114111
[mk-app] #416 <= #400 #415
[mk-app] #417 and #414 #416
[mk-app] #418 or #412 #417
[attach-meaning] #393 arith 55295
[mk-app] #419 <= #123 #393
[mk-app] #420 and #340 #419
[attach-meaning] #413 arith 57344
[mk-app] #421 <= #413 #123
[attach-meaning] #415 arith 1114111
[mk-app] #422 <= #123 #415
[mk-app] #423 and #421 #422
[mk-app] #424 or #420 #423
[mk-app] #425 = #123 #400
[mk-app] #426 => #424 #425
[mk-app] #427 and #418 #426
[mk-app] #428 pattern #400
[mk-quant] #429 prelude_char_clip 1 #428 #427
[attach-var-names] #429 (|i| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #430 * #366 #400
[mk-app] #431 >= #400 #337
[inst-discovered] theory-solving 0 arith# ; #403
[mk-app] #430 = #403 #431
[instance] 0 #430
[attach-enode] #430 0
[end-of-instance]
[mk-app] #430 and #431 #394
[attach-meaning] #366 arith (- 1)
[mk-app] #432 * #366 #400
[mk-app] #433 Int
[attach-meaning] #433 arith (- 57344)
[attach-meaning] #413 arith 57344
[mk-app] #434 >= #400 #413
[inst-discovered] theory-solving 0 arith# ; #414
[mk-app] #432 = #414 #434
[instance] 0 #432
[attach-enode] #432 0
[end-of-instance]
[mk-app] #432 and #434 #416
[mk-app] #433 or #430 #432
[attach-meaning] #366 arith (- 1)
[mk-app] #435 * #366 #123
[inst-discovered] theory-solving 0 arith# ; #340
[mk-app] #435 = #340 #349
[instance] 0 #435
[attach-enode] #435 0
[end-of-instance]
[mk-app] #435 and #349 #419
[attach-meaning] #366 arith (- 1)
[mk-app] #436 * #366 #123
[mk-app] #437 Int
[attach-meaning] #437 arith (- 57344)
[attach-meaning] #413 arith 57344
[mk-app] #438 >= #123 #413
[inst-discovered] theory-solving 0 arith# ; #421
[mk-app] #436 = #421 #438
[instance] 0 #436
[attach-enode] #436 0
[end-of-instance]
[mk-app] #436 and #438 #422
[mk-app] #437 or #435 #436
[mk-app] #439 not #437
[mk-app] #440 or #439 #425
[mk-app] #441 => #437 #425
[inst-discovered] theory-solving 0 basic# ; #441
[mk-app] #442 = #441 #440
[instance] 0 #442
[attach-enode] #442 0
[end-of-instance]
[mk-app] #441 and #433 #440
[mk-quant] #442 prelude_char_clip 1 #428 #441
[attach-var-names] #442 (|i| ; |Int|)
[mk-app] #443 uInv #220 #123
[mk-app] #444 = #443 #357
[mk-app] #445 pattern #443
[mk-quant] #446 prelude_u_inv 2 #445 #444
[attach-var-names] #446 (|i| ; |Int|) (|bits| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #447 * #366 #123
[inst-discovered] theory-solving 0 arith# ; #340
[mk-app] #447 = #340 #349
[instance] 0 #447
[attach-enode] #447 0
[end-of-instance]
[mk-app] #447 <= #354 #123
[mk-app] #448 not #447
[inst-discovered] theory-solving 0 arith# ; #356
[mk-app] #449 = #356 #448
[instance] 0 #449
[attach-enode] #449 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #449 * #366 #123
[mk-app] #450 + #449 #354
[attach-meaning] #366 arith (- 1)
[inst-discovered] theory-solving 0 arith# ; #447
[mk-app] #449 = #447 #373
[instance] 0 #449
[attach-enode] #449 0
[end-of-instance]
[mk-app] #449 = #443 #376
[mk-quant] #450 prelude_u_inv 2 #445 #449
[attach-var-names] #450 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #447 iInv #220 #123
[mk-app] #448 = #447 #384
[mk-app] #451 pattern #447
[mk-quant] #452 prelude_i_inv 2 #451 #448
[attach-var-names] #452 (|i| ; |Int|) (|bits| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #453 * #366 #123
[mk-app] #454 + #453 #363
[attach-meaning] #366 arith (- 1)
[inst-discovered] theory-solving 0 arith# ; #382
[mk-app] #453 = #382 #399
[instance] 0 #453
[attach-enode] #453 0
[end-of-instance]
[mk-app] #453 <= #372 #123
[mk-app] #454 not #453
[inst-discovered] theory-solving 0 arith# ; #383
[mk-app] #455 = #383 #454
[instance] 0 #455
[attach-enode] #455 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #455 * #366 #123
[mk-app] #456 + #455 #372
[attach-meaning] #366 arith (- 1)
[inst-discovered] theory-solving 0 arith# ; #453
[mk-app] #455 = #453 #404
[instance] 0 #455
[attach-enode] #455 0
[end-of-instance]
[mk-app] #455 = #447 #407
[mk-quant] #456 prelude_i_inv 2 #451 #455
[attach-var-names] #456 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #453 charInv #123
[attach-meaning] #393 arith 55295
[attach-meaning] #413 arith 57344
[attach-meaning] #415 arith 1114111
[mk-app] #454 = #453 #424
[mk-app] #457 pattern #453
[mk-quant] #458 prelude_char_inv 1 #457 #454
[attach-var-names] #458 (|i| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #459 * #366 #123
[inst-discovered] theory-solving 0 arith# ; #340
[mk-app] #459 = #340 #349
[instance] 0 #459
[attach-enode] #459 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #459 * #366 #123
[mk-app] #460 Int
[attach-meaning] #460 arith (- 57344)
[attach-meaning] #413 arith 57344
[inst-discovered] theory-solving 0 arith# ; #421
[mk-app] #459 = #421 #438
[instance] 0 #459
[attach-enode] #459 0
[end-of-instance]
[mk-app] #459 = #453 #437
[mk-quant] #460 prelude_char_inv 1 #457 #459
[attach-var-names] #460 (|i| ; |Int|)
[mk-app] #461 has_type #166 #185
[mk-app] #462 pattern #461
[mk-quant] #463 prelude_has_type_int 1 #462 #461
[attach-var-names] #463 (|x| ; |Int|)
[mk-app] #464 has_type #166 #196
[mk-app] #465 => #340 #464
[mk-app] #466 pattern #464
[mk-quant] #467 prelude_has_type_nat 1 #466 #465
[attach-var-names] #467 (|x| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #468 * #366 #123
[inst-discovered] theory-solving 0 arith# ; #340
[mk-app] #468 = #340 #349
[instance] 0 #468
[attach-enode] #468 0
[end-of-instance]
[mk-app] #468 or #346 #464
[mk-app] #469 => #349 #464
[inst-discovered] theory-solving 0 basic# ; #469
[mk-app] #470 = #469 #468
[instance] 0 #470
[attach-enode] #470 0
[end-of-instance]
[mk-quant] #469 prelude_has_type_nat 1 #466 #468
[attach-var-names] #469 (|x| ; |Int|)
[mk-app] #470 uInv #270 #123
[mk-app] #471 has_type #166 #204
[mk-app] #472 => #470 #471
[mk-app] #473 pattern #471
[mk-quant] #474 prelude_has_type_usize 1 #473 #472
[attach-var-names] #474 (|x| ; |Int|)
[mk-app] #475 not #470
[mk-app] #476 or #475 #471
[inst-discovered] theory-solving 0 basic# ; #472
[mk-app] #477 = #472 #476
[instance] 0 #477
[attach-enode] #477 0
[end-of-instance]
[mk-quant] #477 prelude_has_type_usize 1 #473 #476
[attach-var-names] #477 (|x| ; |Int|)
[mk-app] #478 iInv #270 #123
[mk-app] #479 has_type #166 #212
[mk-app] #480 => #478 #479
[mk-app] #481 pattern #479
[mk-quant] #482 prelude_has_type_isize 1 #481 #480
[attach-var-names] #482 (|x| ; |Int|)
[mk-app] #483 not #478
[mk-app] #484 or #483 #479
[inst-discovered] theory-solving 0 basic# ; #480
[mk-app] #485 = #480 #484
[instance] 0 #485
[attach-enode] #485 0
[end-of-instance]
[mk-quant] #485 prelude_has_type_isize 1 #481 #484
[attach-var-names] #485 (|x| ; |Int|)
[mk-app] #486 has_type #166 #221
[mk-app] #487 => #443 #486
[mk-app] #488 pattern #486
[mk-quant] #489 prelude_has_type_uint 2 #488 #487
[attach-var-names] #489 (|x| ; |Int|) (|bits| ; |Int|)
[mk-app] #490 not #443
[mk-app] #491 or #490 #486
[inst-discovered] theory-solving 0 basic# ; #487
[mk-app] #492 = #487 #491
[instance] 0 #492
[attach-enode] #492 0
[end-of-instance]
[mk-quant] #492 prelude_has_type_uint 2 #488 #491
[attach-var-names] #492 (|x| ; |Int|) (|bits| ; |Int|)
[mk-app] #493 has_type #166 #229
[mk-app] #494 => #447 #493
[mk-app] #495 pattern #493
[mk-quant] #496 prelude_has_type_sint 2 #495 #494
[attach-var-names] #496 (|x| ; |Int|) (|bits| ; |Int|)
[mk-app] #497 not #447
[mk-app] #498 or #497 #493
[inst-discovered] theory-solving 0 basic# ; #494
[mk-app] #499 = #494 #498
[instance] 0 #499
[attach-enode] #499 0
[end-of-instance]
[mk-quant] #499 prelude_has_type_sint 2 #495 #498
[attach-var-names] #499 (|x| ; |Int|) (|bits| ; |Int|)
[mk-app] #500 has_type #166 #237
[mk-app] #501 => #443 #500
[mk-app] #502 pattern #500
[mk-quant] #503 prelude_has_type_sint 2 #502 #501
[attach-var-names] #503 (|x| ; |Int|) (|bits| ; |Int|)
[mk-app] #504 or #490 #500
[inst-discovered] theory-solving 0 basic# ; #501
[mk-app] #505 = #501 #504
[instance] 0 #505
[attach-enode] #505 0
[end-of-instance]
[mk-quant] #505 prelude_has_type_sint 2 #502 #504
[attach-var-names] #505 (|x| ; |Int|) (|bits| ; |Int|)
[mk-app] #506 has_type #166 #245
[mk-app] #507 => #453 #506
[mk-app] #508 pattern #506
[mk-quant] #509 prelude_has_type_char 1 #508 #507
[attach-var-names] #509 (|x| ; |Int|)
[mk-app] #510 not #453
[mk-app] #511 or #510 #506
[inst-discovered] theory-solving 0 basic# ; #507
[mk-app] #512 = #507 #511
[instance] 0 #512
[attach-enode] #512 0
[end-of-instance]
[mk-quant] #512 prelude_has_type_char 1 #508 #511
[attach-var-names] #512 (|x| ; |Int|)
[mk-app] #513 <= #337 #187
[mk-app] #514 => #197 #513
[mk-quant] #515 prelude_unbox_int 1 #199 #514
[attach-var-names] #515 (|x| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #516 * #366 #187
[mk-app] #517 >= #187 #337
[inst-discovered] theory-solving 0 arith# ; #513
[mk-app] #516 = #513 #517
[instance] 0 #516
[attach-enode] #516 0
[end-of-instance]
[mk-app] #516 or #201 #517
[mk-app] #518 => #197 #517
[inst-discovered] theory-solving 0 basic# ; #518
[mk-app] #519 = #518 #516
[instance] 0 #519
[attach-enode] #519 0
[end-of-instance]
[mk-quant] #518 prelude_unbox_int 1 #199 #516
[attach-var-names] #518 (|x| ; |Poly|)
[mk-app] #519 uInv #270 #187
[mk-app] #520 => #205 #519
[mk-quant] #521 prelude_unbox_usize 1 #207 #520
[attach-var-names] #521 (|x| ; |Poly|)
[mk-app] #522 or #209 #519
[inst-discovered] theory-solving 0 basic# ; #520
[mk-app] #523 = #520 #522
[instance] 0 #523
[attach-enode] #523 0
[end-of-instance]
[mk-quant] #523 prelude_unbox_usize 1 #207 #522
[attach-var-names] #523 (|x| ; |Poly|)
[mk-app] #524 iInv #270 #187
[mk-app] #525 => #213 #524
[mk-quant] #526 prelude_unbox_isize 1 #215 #525
[attach-var-names] #526 (|x| ; |Poly|)
[mk-app] #527 or #217 #524
[inst-discovered] theory-solving 0 basic# ; #525
[mk-app] #528 = #525 #527
[instance] 0 #528
[attach-enode] #528 0
[end-of-instance]
[mk-quant] #528 prelude_unbox_isize 1 #215 #527
[attach-var-names] #528 (|x| ; |Poly|)
[mk-app] #529 uInv #220 #187
[mk-app] #530 => #222 #529
[mk-quant] #531 prelude_unbox_uint 2 #224 #530
[attach-var-names] #531 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #532 or #226 #529
[inst-discovered] theory-solving 0 basic# ; #530
[mk-app] #533 = #530 #532
[instance] 0 #533
[attach-enode] #533 0
[end-of-instance]
[mk-quant] #533 prelude_unbox_uint 2 #224 #532
[attach-var-names] #533 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #534 iInv #220 #187
[mk-app] #535 => #230 #534
[mk-quant] #536 prelude_unbox_sint 2 #232 #535
[attach-var-names] #536 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #537 or #234 #534
[inst-discovered] theory-solving 0 basic# ; #535
[mk-app] #538 = #535 #537
[instance] 0 #538
[attach-enode] #538 0
[end-of-instance]
[mk-quant] #538 prelude_unbox_sint 2 #232 #537
[attach-var-names] #538 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #539 => #238 #529
[mk-quant] #540 prelude_unbox_sint 2 #240 #539
[attach-var-names] #540 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #541 or #242 #529
[inst-discovered] theory-solving 0 basic# ; #539
[mk-app] #542 = #539 #541
[instance] 0 #542
[attach-enode] #542 0
[end-of-instance]
[mk-quant] #542 prelude_unbox_sint 2 #240 #541
[attach-var-names] #542 (|x| ; |Poly|) (|bits| ; |Int|)
[mk-app] #543 Add #220 #123
[mk-app] #544 + #220 #123
[mk-app] #545 = #543 #544
[mk-app] #546 pattern #543
[mk-quant] #547 prelude_add 2 #546 #545
[attach-var-names] #547 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #548 + #123 #220
[inst-discovered] theory-solving 0 arith# ; #544
[mk-app] #549 = #544 #548
[instance] 0 #549
[attach-enode] #549 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #549 * #366 #123
[attach-meaning] #366 arith (- 1)
[mk-app] #550 * #366 #220
[mk-app] #551 + #549 #550 #543
[attach-meaning] #366 arith (- 1)
[mk-app] #552 * #366 #543
[mk-app] #553 + #123 #220 #552
[mk-app] #549 = #553 #337
[mk-app] #550 = #543 #548
[inst-discovered] theory-solving 0 arith# ; #550
[mk-app] #551 = #550 #549
[instance] 0 #551
[attach-enode] #551 0
[end-of-instance]
[mk-quant] #548 prelude_add 2 #546 #549
[attach-var-names] #548 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #550 Sub #220 #123
[mk-app] #551 - #220 #123
[mk-app] #554 = #550 #551
[mk-app] #555 pattern #550
[mk-quant] #556 prelude_sub 2 #555 #554
[attach-var-names] #556 (|y| ; |Int|) (|x| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #557 * #366 #123
[mk-app] #558 + #220 #557
[inst-discovered] theory-solving 0 arith# ; #551
[mk-app] #559 = #551 #558
[instance] 0 #559
[attach-enode] #559 0
[end-of-instance]
[mk-app] #559 + #557 #220
[inst-discovered] theory-solving 0 arith# ; #558
[mk-app] #560 = #558 #559
[instance] 0 #560
[attach-enode] #560 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #560 * #366 #220
[mk-app] #561 + #123 #560 #550
[mk-app] #562 = #561 #337
[mk-app] #563 = #550 #559
[inst-discovered] theory-solving 0 arith# ; #563
[mk-app] #564 = #563 #562
[instance] 0 #564
[attach-enode] #564 0
[end-of-instance]
[mk-quant] #563 prelude_sub 2 #555 #562
[attach-var-names] #563 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #557 Mul #220 #123
[mk-app] #559 * #220 #123
[mk-app] #558 = #557 #559
[mk-app] #564 pattern #557
[mk-quant] #565 prelude_mul 2 #564 #558
[attach-var-names] #565 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #566 * #123 #220
[inst-discovered] theory-solving 0 arith# ; #559
[mk-app] #567 = #559 #566
[instance] 0 #567
[attach-enode] #567 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #567 * #366 #566
[mk-app] #568 + #557 #567
[mk-app] #569 = #568 #337
[mk-app] #570 = #557 #566
[inst-discovered] theory-solving 0 arith# ; #570
[mk-app] #571 = #570 #569
[instance] 0 #571
[attach-enode] #571 0
[end-of-instance]
[mk-quant] #570 prelude_mul 2 #564 #569
[attach-var-names] #570 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #571 EucDiv #220 #123
[mk-app] #572 div #220 #123
[mk-app] #573 = #571 #572
[mk-app] #574 pattern #571
[mk-quant] #575 prelude_eucdiv 2 #574 #573
[attach-var-names] #575 (|y| ; |Int|) (|x| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #576 * #366 #572
[mk-app] #577 + #571 #576
[mk-app] #578 = #577 #337
[inst-discovered] theory-solving 0 arith# ; #573
[mk-app] #579 = #573 #578
[instance] 0 #579
[attach-enode] #579 0
[end-of-instance]
[mk-quant] #579 prelude_eucdiv 2 #574 #578
[attach-var-names] #579 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #580 EucMod #220 #123
[mk-app] #581 mod #220 #123
[mk-app] #582 = #580 #581
[mk-app] #583 pattern #580
[mk-quant] #584 prelude_eucmod 2 #583 #582
[attach-var-names] #584 (|y| ; |Int|) (|x| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #585 * #366 #581
[mk-app] #586 + #580 #585
[mk-app] #587 = #586 #337
[inst-discovered] theory-solving 0 arith# ; #582
[mk-app] #588 = #582 #587
[instance] 0 #588
[attach-enode] #588 0
[end-of-instance]
[mk-quant] #588 prelude_eucmod 2 #583 #587
[attach-var-names] #588 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #589 RAdd #8 #7
[mk-app] #590 + #8 #7
[mk-app] #591 = #589 #590
[mk-app] #592 pattern #589
[mk-quant] #593 prelude_radd 2 #592 #591
[attach-var-names] #593 (|y| ; |Real|) (|x| ; |Real|)
[mk-app] #594 + #7 #8
[inst-discovered] theory-solving 0 arith# ; #590
[mk-app] #595 = #590 #594
[instance] 0 #595
[attach-enode] #595 0
[end-of-instance]
[mk-app] #595 Real
[attach-meaning] #595 arith (- 1)
[mk-app] #596 * #595 #7
[attach-meaning] #595 arith (- 1)
[mk-app] #597 * #595 #8
[mk-app] #598 Real
[attach-meaning] #598 arith 0
[mk-app] #599 + #596 #597 #589
[attach-meaning] #595 arith (- 1)
[mk-app] #600 * #595 #589
[mk-app] #601 + #7 #8 #600
[mk-app] #596 = #601 #598
[mk-app] #597 = #589 #594
[inst-discovered] theory-solving 0 arith# ; #597
[mk-app] #599 = #597 #596
[instance] 0 #599
[attach-enode] #599 0
[end-of-instance]
[mk-quant] #594 prelude_radd 2 #592 #596
[attach-var-names] #594 (|y| ; |Real|) (|x| ; |Real|)
[mk-app] #597 RSub #8 #7
[mk-app] #599 - #8 #7
[mk-app] #602 = #597 #599
[mk-app] #603 pattern #597
[mk-quant] #604 prelude_rsub 2 #603 #602
[attach-var-names] #604 (|y| ; |Real|) (|x| ; |Real|)
[attach-meaning] #595 arith (- 1)
[mk-app] #605 * #595 #7
[mk-app] #606 + #8 #605
[inst-discovered] theory-solving 0 arith# ; #599
[mk-app] #607 = #599 #606
[instance] 0 #607
[attach-enode] #607 0
[end-of-instance]
[mk-app] #607 + #605 #8
[inst-discovered] theory-solving 0 arith# ; #606
[mk-app] #608 = #606 #607
[instance] 0 #608
[attach-enode] #608 0
[end-of-instance]
[attach-meaning] #595 arith (- 1)
[mk-app] #608 * #595 #8
[mk-app] #609 + #7 #608 #597
[mk-app] #610 = #609 #598
[mk-app] #611 = #597 #607
[inst-discovered] theory-solving 0 arith# ; #611
[mk-app] #612 = #611 #610
[instance] 0 #612
[attach-enode] #612 0
[end-of-instance]
[mk-quant] #611 prelude_rsub 2 #603 #610
[attach-var-names] #611 (|y| ; |Real|) (|x| ; |Real|)
[mk-app] #605 RMul #8 #7
[mk-app] #607 * #8 #7
[mk-app] #606 = #605 #607
[mk-app] #612 pattern #605
[mk-quant] #613 prelude_rmul 2 #612 #606
[attach-var-names] #613 (|y| ; |Real|) (|x| ; |Real|)
[mk-app] #614 * #7 #8
[inst-discovered] theory-solving 0 arith# ; #607
[mk-app] #615 = #607 #614
[instance] 0 #615
[attach-enode] #615 0
[end-of-instance]
[attach-meaning] #595 arith (- 1)
[mk-app] #615 * #595 #614
[mk-app] #616 + #605 #615
[mk-app] #617 = #616 #598
[mk-app] #618 = #605 #614
[inst-discovered] theory-solving 0 arith# ; #618
[mk-app] #619 = #618 #617
[instance] 0 #619
[attach-enode] #619 0
[end-of-instance]
[mk-quant] #618 prelude_rmul 2 #612 #617
[attach-var-names] #618 (|y| ; |Real|) (|x| ; |Real|)
[mk-app] #619 RDiv #8 #7
[mk-app] #620 / #8 #7
[mk-app] #621 = #619 #620
[mk-app] #622 pattern #619
[mk-quant] #623 prelude_rdiv 2 #622 #621
[attach-var-names] #623 (|y| ; |Real|) (|x| ; |Real|)
[attach-meaning] #595 arith (- 1)
[mk-app] #624 * #595 #620
[mk-app] #625 + #619 #624
[mk-app] #626 = #625 #598
[inst-discovered] theory-solving 0 arith# ; #621
[mk-app] #627 = #621 #626
[instance] 0 #627
[attach-enode] #627 0
[end-of-instance]
[mk-quant] #627 prelude_rdiv 2 #622 #626
[attach-var-names] #627 (|y| ; |Real|) (|x| ; |Real|)
[mk-app] #628 <= #337 #220
[mk-app] #629 and #628 #340
[mk-app] #630 <= #337 #557
[mk-app] #631 => #629 #630
[mk-quant] #632 prelude_mul_nats 2 #564 #631
[attach-var-names] #632 (|y| ; |Int|) (|x| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #633 >= #220 #337
[inst-discovered] theory-solving 0 arith# ; #628
[mk-app] #634 = #628 #633
[instance] 0 #634
[attach-enode] #634 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #634 * #366 #123
[inst-discovered] theory-solving 0 arith# ; #340
[mk-app] #634 = #340 #349
[instance] 0 #634
[attach-enode] #634 0
[end-of-instance]
[mk-app] #634 and #633 #349
[attach-meaning] #366 arith (- 1)
[mk-app] #635 * #366 #557
[mk-app] #636 >= #557 #337
[inst-discovered] theory-solving 0 arith# ; #630
[mk-app] #635 = #630 #636
[instance] 0 #635
[attach-enode] #635 0
[end-of-instance]
[mk-app] #635 not #634
[mk-app] #637 or #635 #636
[mk-app] #638 => #634 #636
[inst-discovered] theory-solving 0 basic# ; #638
[mk-app] #639 = #638 #637
[instance] 0 #639
[attach-enode] #639 0
[end-of-instance]
[mk-quant] #638 prelude_mul_nats 2 #564 #637
[attach-var-names] #638 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #639 < #337 #123
[mk-app] #640 and #628 #639
[mk-app] #641 <= #337 #571
[mk-app] #642 <= #571 #220
[mk-app] #643 and #641 #642
[mk-app] #644 => #640 #643
[mk-quant] #645 prelude_div_unsigned_in_bounds 2 #574 #644
[attach-var-names] #645 (|y| ; |Int|) (|x| ; |Int|)
[attach-meaning] #366 arith (- 1)
[inst-discovered] theory-solving 0 arith# ; #628
[mk-app] #646 = #628 #633
[instance] 0 #646
[attach-enode] #646 0
[end-of-instance]
[mk-app] #646 <= #123 #337
[mk-app] #647 not #646
[inst-discovered] theory-solving 0 arith# ; #639
[mk-app] #648 = #639 #647
[instance] 0 #648
[attach-enode] #648 0
[end-of-instance]
[mk-app] #648 and #633 #647
[attach-meaning] #366 arith (- 1)
[mk-app] #649 * #366 #571
[mk-app] #650 >= #571 #337
[inst-discovered] theory-solving 0 arith# ; #641
[mk-app] #649 = #641 #650
[instance] 0 #649
[attach-enode] #649 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #649 + #560 #571
[attach-meaning] #366 arith (- 1)
[mk-app] #651 * #366 #571
[mk-app] #652 + #220 #651
[mk-app] #649 >= #652 #337
[inst-discovered] theory-solving 0 arith# ; #642
[mk-app] #653 = #642 #649
[instance] 0 #653
[attach-enode] #653 0
[end-of-instance]
[mk-app] #653 and #650 #649
[mk-app] #654 not #648
[mk-app] #655 or #654 #653
[mk-app] #656 => #648 #653
[inst-discovered] theory-solving 0 basic# ; #656
[mk-app] #657 = #656 #655
[instance] 0 #657
[attach-enode] #657 0
[end-of-instance]
[mk-quant] #656 prelude_div_unsigned_in_bounds 2 #574 #655
[attach-var-names] #656 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #657 <= #337 #580
[mk-app] #658 < #580 #123
[mk-app] #659 and #657 #658
[mk-app] #660 => #640 #659
[mk-quant] #661 prelude_mod_unsigned_in_bounds 2 #583 #660
[attach-var-names] #661 (|y| ; |Int|) (|x| ; |Int|)
[attach-meaning] #366 arith (- 1)
[inst-discovered] theory-solving 0 arith# ; #628
[mk-app] #662 = #628 #633
[instance] 0 #662
[attach-enode] #662 0
[end-of-instance]
[inst-discovered] theory-solving 0 arith# ; #639
[mk-app] #662 = #639 #647
[instance] 0 #662
[attach-enode] #662 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #662 * #366 #580
[mk-app] #663 >= #580 #337
[inst-discovered] theory-solving 0 arith# ; #657
[mk-app] #662 = #657 #663
[instance] 0 #662
[attach-enode] #662 0
[end-of-instance]
[mk-app] #662 <= #123 #580
[mk-app] #664 not #662
[inst-discovered] theory-solving 0 arith# ; #658
[mk-app] #665 = #658 #664
[instance] 0 #665
[attach-enode] #665 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #665 * #366 #580
[mk-app] #666 + #123 #665
[mk-app] #667 <= #666 #337
[inst-discovered] theory-solving 0 arith# ; #662
[mk-app] #668 = #662 #667
[instance] 0 #668
[attach-enode] #668 0
[end-of-instance]
[mk-app] #668 not #667
[mk-app] #669 and #663 #668
[mk-app] #670 or #654 #669
[mk-app] #671 => #648 #669
[inst-discovered] theory-solving 0 basic# ; #671
[mk-app] #672 = #671 #670
[instance] 0 #672
[attach-enode] #672 0
[end-of-instance]
[mk-quant] #671 prelude_mod_unsigned_in_bounds 2 #583 #670
[attach-var-names] #671 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #662 %I #44
[mk-app] #664 uInv #123 #662
[mk-app] #672 %I #33
[mk-app] #673 uInv #123 #672
[mk-app] #674 and #664 #673
[mk-app] #675 bitxor #44 #33
[mk-app] #676 uInv #123 #675
[mk-app] #677 => #674 #676
[mk-app] #678 uClip #123 #675
[mk-app] #679 pattern #678
[mk-quant] #680 prelude_bit_xor_u_inv 3 #679 #677
[attach-var-names] #680 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #681 not #674
[mk-app] #682 or #681 #676
[inst-discovered] theory-solving 0 basic# ; #677
[mk-app] #683 = #677 #682
[instance] 0 #683
[attach-enode] #683 0
[end-of-instance]
[mk-quant] #683 prelude_bit_xor_u_inv 3 #679 #682
[attach-var-names] #683 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #684 iInv #123 #662
[mk-app] #685 iInv #123 #672
[mk-app] #686 and #684 #685
[mk-app] #687 iInv #123 #675
[mk-app] #688 => #686 #687
[mk-app] #689 iClip #123 #675
[mk-app] #690 pattern #689
[mk-quant] #691 prelude_bit_xor_i_inv 3 #690 #688
[attach-var-names] #691 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #692 not #686
[mk-app] #693 or #692 #687
[inst-discovered] theory-solving 0 basic# ; #688
[mk-app] #694 = #688 #693
[instance] 0 #694
[attach-enode] #694 0
[end-of-instance]
[mk-quant] #694 prelude_bit_xor_i_inv 3 #690 #693
[attach-var-names] #694 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #695 bitor #44 #33
[mk-app] #696 uInv #123 #695
[mk-app] #697 => #674 #696
[mk-app] #698 uClip #123 #695
[mk-app] #699 pattern #698
[mk-quant] #700 prelude_bit_or_u_inv 3 #699 #697
[attach-var-names] #700 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #701 or #681 #696
[inst-discovered] theory-solving 0 basic# ; #697
[mk-app] #702 = #697 #701
[instance] 0 #702
[attach-enode] #702 0
[end-of-instance]
[mk-quant] #702 prelude_bit_or_u_inv 3 #699 #701
[attach-var-names] #702 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #703 iInv #123 #695
[mk-app] #704 => #686 #703
[mk-app] #705 iClip #123 #695
[mk-app] #706 pattern #705
[mk-quant] #707 prelude_bit_or_i_inv 3 #706 #704
[attach-var-names] #707 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #708 or #692 #703
[inst-discovered] theory-solving 0 basic# ; #704
[mk-app] #709 = #704 #708
[instance] 0 #709
[attach-enode] #709 0
[end-of-instance]
[mk-quant] #709 prelude_bit_or_i_inv 3 #706 #708
[attach-var-names] #709 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #710 bitand #44 #33
[mk-app] #711 uInv #123 #710
[mk-app] #712 => #674 #711
[mk-app] #713 uClip #123 #710
[mk-app] #714 pattern #713
[mk-quant] #715 prelude_bit_and_u_inv 3 #714 #712
[attach-var-names] #715 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #716 or #681 #711
[inst-discovered] theory-solving 0 basic# ; #712
[mk-app] #717 = #712 #716
[instance] 0 #717
[attach-enode] #717 0
[end-of-instance]
[mk-quant] #717 prelude_bit_and_u_inv 3 #714 #716
[attach-var-names] #717 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #718 iInv #123 #710
[mk-app] #719 => #686 #718
[mk-app] #720 iClip #123 #710
[mk-app] #721 pattern #720
[mk-quant] #722 prelude_bit_and_i_inv 3 #721 #719
[attach-var-names] #722 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #723 or #692 #718
[inst-discovered] theory-solving 0 basic# ; #719
[mk-app] #724 = #719 #723
[instance] 0 #724
[attach-enode] #724 0
[end-of-instance]
[mk-quant] #724 prelude_bit_and_i_inv 3 #721 #723
[attach-var-names] #724 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #725 <= #337 #672
[mk-app] #726 and #664 #725
[mk-app] #727 bitshr #44 #33
[mk-app] #728 uInv #123 #727
[mk-app] #729 => #726 #728
[mk-app] #730 uClip #123 #727
[mk-app] #731 pattern #730
[mk-quant] #732 prelude_bit_shr_u_inv 3 #731 #729
[attach-var-names] #732 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #733 * #366 #672
[mk-app] #734 >= #672 #337
[inst-discovered] theory-solving 0 arith# ; #725
[mk-app] #733 = #725 #734
[instance] 0 #733
[attach-enode] #733 0
[end-of-instance]
[mk-app] #733 and #664 #734
[mk-app] #735 not #733
[mk-app] #736 or #735 #728
[mk-app] #737 => #733 #728
[inst-discovered] theory-solving 0 basic# ; #737
[mk-app] #738 = #737 #736
[instance] 0 #738
[attach-enode] #738 0
[end-of-instance]
[mk-quant] #737 prelude_bit_shr_u_inv 3 #731 #736
[attach-var-names] #737 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #738 and #684 #725
[mk-app] #739 iInv #123 #727
[mk-app] #740 => #738 #739
[mk-app] #741 iClip #123 #727
[mk-app] #742 pattern #741
[mk-quant] #743 prelude_bit_shr_i_inv 3 #742 #740
[attach-var-names] #743 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #744 * #366 #672
[inst-discovered] theory-solving 0 arith# ; #725
[mk-app] #744 = #725 #734
[instance] 0 #744
[attach-enode] #744 0
[end-of-instance]
[mk-app] #744 and #684 #734
[mk-app] #745 not #744
[mk-app] #746 or #745 #739
[mk-app] #747 => #744 #739
[inst-discovered] theory-solving 0 basic# ; #747
[mk-app] #748 = #747 #746
[instance] 0 #748
[attach-enode] #748 0
[end-of-instance]
[mk-quant] #747 prelude_bit_shr_i_inv 3 #742 #746
[attach-var-names] #747 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #748 = #123 #337
[mk-app] #749 not #748
[mk-app] #750 singular_mod #220 #123
[mk-app] #751 = #580 #750
[mk-app] #752 => #749 #751
[mk-app] #753 pattern #750
[mk-quant] #754 prelude_singularmod 2 #753 #752
[attach-var-names] #754 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #755 or #748 #751
[inst-discovered] theory-solving 0 basic# ; #752
[mk-app] #756 = #752 #755
[instance] 0 #756
[attach-enode] #756 0
[end-of-instance]
[mk-quant] #756 prelude_singularmod 2 #753 #755
[attach-var-names] #756 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #757 check_decrease_height #44 #33 #129
[mk-app] #758 height #44
[mk-app] #759 height #33
[mk-app] #760 height_lt #758 #759
[mk-app] #761 = #758 #759
[mk-app] #762 and #761 #129
[mk-app] #763 or #760 #762
[mk-app] #764 = #757 #763
[mk-app] #765 pattern #757
[mk-quant] #766 prelude_check_decrease_height 3 #765 #764
[attach-var-names] #766 (|otherwise| ; |Bool|) (|prev| ; |Poly|) (|cur| ; |Poly|)
[mk-app] #767 I #220
[mk-app] #768 height #767
[mk-app] #769 height #166
[mk-app] #770 height_lt #768 #769
[mk-app] #771 < #220 #123
[mk-app] #772 and #628 #771
[mk-app] #773 = #770 #772
[mk-app] #774 pattern #770
[mk-quant] #775 prelude_check_decrease_int_height 2 #774 #773
[attach-var-names] #775 (|prev| ; |Int|) (|cur| ; |Int|)
[attach-meaning] #366 arith (- 1)
[inst-discovered] theory-solving 0 arith# ; #628
[mk-app] #776 = #628 #633
[instance] 0 #776
[attach-enode] #776 0
[end-of-instance]
[mk-app] #776 <= #123 #220
[mk-app] #777 not #776
[inst-discovered] theory-solving 0 arith# ; #771
[mk-app] #778 = #771 #777
[instance] 0 #778
[attach-enode] #778 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #778 + #123 #560
[mk-app] #779 <= #778 #337
[inst-discovered] theory-solving 0 arith# ; #776
[mk-app] #780 = #776 #779
[instance] 0 #780
[attach-enode] #780 0
[end-of-instance]
[mk-app] #780 not #779
[mk-app] #781 and #633 #780
[mk-app] #782 = #770 #781
[mk-quant] #783 prelude_check_decrease_int_height 2 #774 #782
[attach-var-names] #783 (|prev| ; |Int|) (|cur| ; |Int|)
[mk-var] #776 1
[mk-var] #777 0
[mk-app] #784 height_lt #776 #777
[mk-app] #785 partial-order #776 #777
[mk-app] #786 = #776 #777
[mk-app] #787 not #786
[mk-app] #788 and #785 #787
[mk-app] #789 = #784 #788
[mk-app] #790 pattern #784
[mk-quant] #791 prelude_height_lt 2 #790 #789
[attach-var-names] #791 (|y| ; |Height|) (|x| ; |Height|)
[mk-app] #792 fuel%vstd!function.axiom_fn_mut_call_requires.
[mk-app] #793 fuel%vstd!function.axiom_fn_mut_call_ensures.
[mk-app] #794 fuel%the_q!model.pow2.
[mk-app] #795 fuel%the_q!model.abs_int.
[mk-app] #796 fuel%the_q!model.max_int.
[mk-app] #797 fuel%the_q!model.divides.
[mk-app] #798 fuel%the_q!model.gcd_nat.
[mk-app] #799 fuel%the_q!model.gcd_int.
[mk-app] #800 fuel%the_q!model.bitlen.
[mk-app] #801 fuel%the_q!model.max_mag.
[mk-app] #802 fuel%the_q!model.fits_budget.
[mk-app] #803 fuel%the_q!model.magnitude_fits.
[mk-app] #804 fuel%the_q!model.impl&%0.wf.
[mk-app] #805 fuel%the_q!model.impl&%0.n.
[mk-app] #806 fuel%the_q!model.impl&%0.d.
[mk-app] #807 fuel%the_q!model.q_eq.
[mk-app] #808 fuel%the_q!model.q_le.
[mk-app] #809 fuel%the_q!model.q_lt.
[mk-app] #810 fuel%the_q!model.q_is.
[mk-app] #811 fuel%the_q!model.q_le_frac.
[mk-app] #812 fuel%the_q!model.q_ge_frac.
[mk-app] #813 fuel%the_q!model.precision_b.
[mk-app] #814 fuel%the_q!model.within_error_bound.
[mk-app] #815 fuel%the_q!model.within_error_bound_k.
[mk-app] #816 fuel%the_q!model.within_abs_error.
[mk-app] #817 fuel%the_q!types.MAX_MAG.
[mk-app] #818 fuel%vstd!array.group_array_axioms.
[mk-app] #819 fuel%vstd!function.group_function_axioms.
[mk-app] #820 fuel%vstd!imap.group_imap_lemmas.
[mk-app] #821 fuel%vstd!iset.group_iset_lemmas.
[mk-app] #822 fuel%vstd!laws_cmp.group_laws_cmp.
[mk-app] #823 fuel%vstd!laws_eq.bool_laws.group_laws_eq.
[mk-app] #824 fuel%vstd!laws_eq.u8_laws.group_laws_eq.
[mk-app] #825 fuel%vstd!laws_eq.i8_laws.group_laws_eq.
[mk-app] #826 fuel%vstd!laws_eq.u16_laws.group_laws_eq.
[mk-app] #827 fuel%vstd!laws_eq.i16_laws.group_laws_eq.
[mk-app] #828 fuel%vstd!laws_eq.u32_laws.group_laws_eq.
[mk-app] #829 fuel%vstd!laws_eq.i32_laws.group_laws_eq.
[mk-app] #830 fuel%vstd!laws_eq.u64_laws.group_laws_eq.
[mk-app] #831 fuel%vstd!laws_eq.i64_laws.group_laws_eq.
[mk-app] #832 fuel%vstd!laws_eq.u128_laws.group_laws_eq.
[mk-app] #833 fuel%vstd!laws_eq.i128_laws.group_laws_eq.
[mk-app] #834 fuel%vstd!laws_eq.usize_laws.group_laws_eq.
[mk-app] #835 fuel%vstd!laws_eq.isize_laws.group_laws_eq.
[mk-app] #836 fuel%vstd!laws_eq.tuple_1_laws.group_laws_eq.
[mk-app] #837 fuel%vstd!laws_eq.tuple_2_laws.group_laws_eq.
[mk-app] #838 fuel%vstd!laws_eq.tuple_3_laws.group_laws_eq.
[mk-app] #839 fuel%vstd!laws_eq.tuple_4_laws.group_laws_eq.
[mk-app] #840 fuel%vstd!laws_eq.tuple_5_laws.group_laws_eq.
[mk-app] #841 fuel%vstd!laws_eq.tuple_6_laws.group_laws_eq.
[mk-app] #842 fuel%vstd!laws_eq.tuple_7_laws.group_laws_eq.
[mk-app] #843 fuel%vstd!laws_eq.tuple_8_laws.group_laws_eq.
[mk-app] #844 fuel%vstd!laws_eq.tuple_9_laws.group_laws_eq.
[mk-app] #845 fuel%vstd!laws_eq.tuple_10_laws.group_laws_eq.
[mk-app] #846 fuel%vstd!laws_eq.tuple_11_laws.group_laws_eq.
[mk-app] #847 fuel%vstd!laws_eq.tuple_12_laws.group_laws_eq.
[mk-app] #848 fuel%vstd!laws_eq.group_laws_eq.
[mk-app] #849 fuel%vstd!layout.group_align_properties.
[mk-app] #850 fuel%vstd!layout.group_layout_axioms.
[mk-app] #851 fuel%vstd!map.group_map_lemmas.
[mk-app] #852 fuel%vstd!multiset.group_multiset_axioms.
[mk-app] #853 fuel%vstd!raw_ptr.group_raw_ptr_axioms.
[mk-app] #854 fuel%vstd!seq.group_seq_lemmas.
[mk-app] #855 fuel%vstd!seq_lib.group_filter_ensures.
[mk-app] #856 fuel%vstd!seq_lib.group_seq_lib_default.
[mk-app] #857 fuel%vstd!set.group_set_lemmas.
[mk-app] #858 fuel%vstd!set_lib.group_set_lib_default.
[mk-app] #859 fuel%vstd!slice.group_slice_axioms.
[mk-app] #860 fuel%vstd!string.group_string_axioms.
[mk-app] #861 fuel%vstd!std_specs.bits.group_bits_axioms.
[mk-app] #862 fuel%vstd!std_specs.control_flow.group_control_flow_axioms.
[mk-app] #863 fuel%vstd!std_specs.iter.group_iter_axioms.
[mk-app] #864 fuel%vstd!std_specs.manually_drop.group_manually_drop_axioms.
[mk-app] #865 fuel%vstd!std_specs.btree.group_btree_axioms.
[mk-app] #866 fuel%vstd!std_specs.hash.group_hash_axioms.
[mk-app] #867 fuel%vstd!std_specs.range.group_range_axioms.
[mk-app] #868 fuel%vstd!std_specs.slice.group_slice_axioms.
[mk-app] #869 fuel%vstd!std_specs.vec.group_vec_axioms.
[mk-app] #870 fuel%vstd!std_specs.vecdeque.group_vec_dequeue_axioms.
[mk-app] #871 fuel%vstd!group_vstd_default.
[mk-app] #872 distinct #792 #793 #794 #795 #796 #797 #798 #799 #800 #801 #802 #803 #804 #805 #806 #807 #808 #809 #810 #811 #812 #813 #814 #815 #816 #817 #818 #819 #820 #821 #822 #823 #824 #825 #826 #827 #828 #829 #830 #831 #832 #833 #834 #835 #836 #837 #838 #839 #840 #841 #842 #843 #844 #845 #846 #847 #848 #849 #850 #851 #852 #853 #854 #855 #856 #857 #858 #859 #860 #861 #862 #863 #864 #865 #866 #867 #868 #869 #870 #871
[mk-app] #873 fuel_bool_default #819
[mk-app] #874 fuel_bool_default #792
[mk-app] #875 fuel_bool_default #793
[mk-app] #876 and #874 #875
[mk-app] #877 => #873 #876
[mk-app] #878 not #873
[mk-app] #879 or #878 #876
[inst-discovered] theory-solving 0 basic# ; #877
[mk-app] #880 = #877 #879
[instance] 0 #880
[attach-enode] #880 0
[end-of-instance]
[mk-app] #880 fuel_bool_default #848
[mk-app] #881 fuel_bool_default #823
[mk-app] #882 fuel_bool_default #824
[mk-app] #883 fuel_bool_default #825
[mk-app] #884 fuel_bool_default #826
[mk-app] #885 fuel_bool_default #827
[mk-app] #886 fuel_bool_default #828
[mk-app] #887 fuel_bool_default #829
[mk-app] #888 fuel_bool_default #830
[mk-app] #889 fuel_bool_default #831
[mk-app] #890 fuel_bool_default #832
[mk-app] #891 fuel_bool_default #833
[mk-app] #892 fuel_bool_default #834
[mk-app] #893 fuel_bool_default #835
[mk-app] #894 fuel_bool_default #836
[mk-app] #895 fuel_bool_default #837
[mk-app] #896 fuel_bool_default #838
[mk-app] #897 fuel_bool_default #839
[mk-app] #898 fuel_bool_default #840
[mk-app] #899 fuel_bool_default #841
[mk-app] #900 fuel_bool_default #842
[mk-app] #901 fuel_bool_default #843
[mk-app] #902 fuel_bool_default #844
[mk-app] #903 fuel_bool_default #845
[mk-app] #904 fuel_bool_default #846
[mk-app] #905 fuel_bool_default #847
[mk-app] #906 and #881 #882 #883 #884 #885 #886 #887 #888 #889 #890 #891 #892 #893 #894 #895 #896 #897 #898 #899 #900 #901 #902 #903 #904 #905
[mk-app] #907 => #880 #906
[mk-app] #908 not #880
[mk-app] #909 or #908 #906
[inst-discovered] theory-solving 0 basic# ; #907
[mk-app] #910 = #907 #909
[instance] 0 #910
[attach-enode] #910 0
[end-of-instance]
[mk-app] #910 fuel_bool_default #850
[mk-app] #911 fuel_bool_default #849
[mk-app] #912 => #910 #911
[mk-app] #913 not #910
[mk-app] #914 or #913 #911
[inst-discovered] theory-solving 0 basic# ; #912
[mk-app] #915 = #912 #914
[instance] 0 #915
[attach-enode] #915 0
[end-of-instance]
[mk-app] #915 fuel_bool_default #856
[mk-app] #916 fuel_bool_default #855
[mk-app] #917 => #915 #916
[mk-app] #918 not #915
[mk-app] #919 or #918 #916
[inst-discovered] theory-solving 0 basic# ; #917
[mk-app] #920 = #917 #919
[instance] 0 #920
[attach-enode] #920 0
[end-of-instance]
[mk-app] #920 fuel_bool_default #871
[mk-app] #921 fuel_bool_default #854
[mk-app] #922 fuel_bool_default #851
[mk-app] #923 fuel_bool_default #857
[mk-app] #924 fuel_bool_default #820
[mk-app] #925 fuel_bool_default #821
[mk-app] #926 fuel_bool_default #858
[mk-app] #927 fuel_bool_default #852
[mk-app] #928 fuel_bool_default #822
[mk-app] #929 fuel_bool_default #859
[mk-app] #930 fuel_bool_default #818
[mk-app] #931 fuel_bool_default #860
[mk-app] #932 fuel_bool_default #853
[mk-app] #933 fuel_bool_default #867
[mk-app] #934 fuel_bool_default #861
[mk-app] #935 fuel_bool_default #862
[mk-app] #936 fuel_bool_default #868
[mk-app] #937 fuel_bool_default #864
[mk-app] #938 fuel_bool_default #863
[mk-app] #939 fuel_bool_default #869
[mk-app] #940 fuel_bool_default #870
[mk-app] #941 fuel_bool_default #866
[mk-app] #942 fuel_bool_default #865
[mk-app] #943 and #921 #915 #922 #923 #924 #925 #926 #927 #873 #880 #928 #929 #930 #931 #932 #910 #933 #934 #935 #936 #937 #938 #939 #940 #941 #942
[mk-app] #944 => #920 #943
[mk-app] #945 not #920
[mk-app] #946 or #945 #943
[inst-discovered] theory-solving 0 basic# ; #944
[mk-app] #947 = #944 #946
[instance] 0 #947
[attach-enode] #947 0
[end-of-instance]
[mk-var] datatype#10 0
[mk-var] datatype#11 1
[mk-app] datatype#12 the_q!types.Q./Q datatype#10 datatype#11
[mk-app] datatype#13 pattern datatype#12
[mk-app] datatype#14 the_q!types.Q./Q/?num datatype#12
[mk-app] datatype#15 = datatype#10 datatype#14
[mk-quant] datatype#16 constructor_accessor_axiom 2 datatype#13 datatype#15
[attach-var-names] datatype#16 (;Int) (;Int)
[mk-app] datatype#17 the_q!types.Q./Q/?den datatype#12
[mk-app] datatype#18 = datatype#11 datatype#17
[mk-quant] datatype#19 constructor_accessor_axiom 2 datatype#13 datatype#18
[attach-var-names] datatype#19 (;Int) (;Int)
[mk-var] #947 0
[mk-app] #948 Poly%the_q!types.Q. #947
[mk-app] #949 %Poly%the_q!types.Q. #948
[mk-app] #950 = #947 #949
[mk-app] #951 pattern #948
[mk-quant] #952 internal_the_q__types__Q_box_axiom_definition 1 #951 #950
[attach-var-names] #952 (|x| ; |the_q!types.Q.|)
[mk-app] #953 TYPE%the_q!types.Q.
[mk-app] #954 has_type #34 #953
[mk-app] #955 %Poly%the_q!types.Q. #34
[mk-app] #956 Poly%the_q!types.Q. #955
[mk-app] #957 = #34 #956
[mk-app] #958 => #954 #957
[mk-app] #959 pattern #954
[mk-quant] #960 internal_the_q__types__Q_unbox_axiom_definition 1 #959 #958
[attach-var-names] #960 (|x| ; |Poly|)
[mk-app] #961 not #954
[mk-app] #962 or #961 #957
[inst-discovered] theory-solving 0 basic# ; #958
[mk-app] #963 = #958 #962
[instance] 0 #963
[attach-enode] #963 0
[end-of-instance]
[mk-quant] #963 internal_the_q__types__Q_unbox_axiom_definition 1 #959 #962
[attach-var-names] #963 (|x| ; |Poly|)
[attach-meaning] #273 arith 64
[mk-app] #964 iInv #273 #220
[attach-meaning] #273 arith 64
[mk-app] #965 iInv #273 #123
[mk-app] #966 and #964 #965
[mk-app] #967 the_q!types.Q./Q #220 #123
[mk-app] #968 Poly%the_q!types.Q. #967
[mk-app] #969 has_type #968 #953
[mk-app] #970 => #966 #969
[mk-app] #971 pattern #969
[mk-quant] #972 internal_the_q!types.Q./Q_constructor_definition 2 #971 #970
[attach-var-names] #972 (|_den!| ; |Int|) (|_num!| ; |Int|)
[mk-app] #973 not #966
[mk-app] #974 or #973 #969
[inst-discovered] theory-solving 0 basic# ; #970
[mk-app] #975 = #970 #974
[instance] 0 #975
[attach-enode] #975 0
[end-of-instance]
[mk-quant] #975 internal_the_q!types.Q./Q_constructor_definition 2 #971 #974
[attach-var-names] #975 (|_den!| ; |Int|) (|_num!| ; |Int|)
[mk-app] #976 the_q!types.Q./Q/num #947
[mk-app] #977 the_q!types.Q./Q/?num #947
[mk-app] #978 = #976 #977
[mk-app] #979 pattern #976
[mk-quant] #980 internal_the_q!types.Q./Q/num_accessor_definition 1 #979 #978
[attach-var-names] #980 (|x| ; |the_q!types.Q.|)
[attach-meaning] #273 arith 64
[mk-app] #981 the_q!types.Q./Q/num #955
[mk-app] #982 iInv #273 #981
[mk-app] #983 => #954 #982
[mk-app] #984 pattern #981 #954
[mk-quant] #985 internal_the_q!types.Q./Q/num_invariant_definition 1 #984 #983
[attach-var-names] #985 (|x| ; |Poly|)
[mk-app] #986 or #961 #982
[inst-discovered] theory-solving 0 basic# ; #983
[mk-app] #987 = #983 #986
[instance] 0 #987
[attach-enode] #987 0
[end-of-instance]
[mk-quant] #987 internal_the_q!types.Q./Q/num_invariant_definition 1 #984 #986
[attach-var-names] #987 (|x| ; |Poly|)
[mk-app] #988 the_q!types.Q./Q/den #947
[mk-app] #989 the_q!types.Q./Q/?den #947
[mk-app] #990 = #988 #989
[mk-app] #991 pattern #988
[mk-quant] #992 internal_the_q!types.Q./Q/den_accessor_definition 1 #991 #990
[attach-var-names] #992 (|x| ; |the_q!types.Q.|)
[attach-meaning] #273 arith 64
[mk-app] #993 the_q!types.Q./Q/den #955
[mk-app] #994 iInv #273 #993
[mk-app] #995 => #954 #994
[mk-app] #996 pattern #993 #954
[mk-quant] #997 internal_the_q!types.Q./Q/den_invariant_definition 1 #996 #995
[attach-var-names] #997 (|x| ; |Poly|)
[mk-app] #998 or #961 #994
[inst-discovered] theory-solving 0 basic# ; #995
[mk-app] #999 = #995 #998
[instance] 0 #999
[attach-enode] #999 0
[end-of-instance]
[mk-quant] #999 internal_the_q!types.Q./Q/den_invariant_definition 1 #996 #998
[attach-var-names] #999 (|x| ; |Poly|)
[mk-var] #1000 0
[mk-app] #1001 Poly%tuple%0. #1000
[mk-app] #1002 %Poly%tuple%0. #1001
[mk-app] #1003 = #1000 #1002
[mk-app] #1004 pattern #1001
[mk-quant] #1005 internal_crate__tuple__0_box_axiom_definition 1 #1004 #1003
[attach-var-names] #1005 (|x| ; |tuple%0.|)
[mk-app] #1006 TYPE%tuple%0.
[mk-app] #1007 has_type #34 #1006
[mk-app] #1008 %Poly%tuple%0. #34
[mk-app] #1009 Poly%tuple%0. #1008
[mk-app] #1010 = #34 #1009
[mk-app] #1011 => #1007 #1010
[mk-app] #1012 pattern #1007
[mk-quant] #1013 internal_crate__tuple__0_unbox_axiom_definition 1 #1012 #1011
[attach-var-names] #1013 (|x| ; |Poly|)
[mk-app] #1014 not #1007
[mk-app] #1015 or #1014 #1010
[inst-discovered] theory-solving 0 basic# ; #1011
[mk-app] #1016 = #1011 #1015
[instance] 0 #1016
[attach-enode] #1016 0
[end-of-instance]
[mk-quant] #1016 internal_crate__tuple__0_unbox_axiom_definition 1 #1012 #1015
[attach-var-names] #1016 (|x| ; |Poly|)
[mk-app] #1017 has_type #1001 #1006
[mk-app] #1018 pattern #1017
[mk-quant] #1019 internal_crate__tuple__0_has_type_always_definition 1 #1018 #1017
[attach-var-names] #1019 (|x| ; |tuple%0.|)
[mk-app] #1020 tr_bound%core!marker.Tuple. #45 #46
[mk-app] #1021 pattern #1020
[mk-quant] #1022 internal_core__marker__Tuple_trait_type_bounds_definition 2 #1021 #1
[attach-var-names] #1022 (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-var] #1023 3
[mk-app] #1024 tr_bound%core!ops.function.FnOnce. #1023 #264 #45 #46
[mk-app] #1025 sized #45
[mk-app] #1026 proj%%core!ops.function.FnOnce./Output #1023 #264 #45 #46
[mk-app] #1027 sized #1026
[mk-app] #1028 and #1025 #1020 #1027
[mk-app] #1029 => #1024 #1028
[mk-app] #1030 pattern #1024
[mk-quant] #1031 internal_core__ops__function__FnOnce_trait_type_bounds_definition 4 #1030 #1029
[attach-var-names] #1031 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1032 not #1024
[mk-app] #1033 or #1032 #1028
[inst-discovered] theory-solving 0 basic# ; #1029
[mk-app] #1034 = #1029 #1033
[instance] 0 #1034
[attach-enode] #1034 0
[end-of-instance]
[mk-quant] #1034 internal_core__ops__function__FnOnce_trait_type_bounds_definition 4 #1030 #1033
[attach-var-names] #1034 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1035 tr_bound%core!ops.function.FnMut. #1023 #264 #45 #46
[mk-app] #1036 and #1024 #1025 #1020
[mk-app] #1037 => #1035 #1036
[mk-app] #1038 pattern #1035
[mk-quant] #1039 internal_core__ops__function__FnMut_trait_type_bounds_definition 4 #1038 #1037
[attach-var-names] #1039 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1040 not #1035
[mk-app] #1041 or #1040 #1036
[inst-discovered] theory-solving 0 basic# ; #1037
[mk-app] #1042 = #1037 #1041
[instance] 0 #1042
[attach-enode] #1042 0
[end-of-instance]
[mk-quant] #1042 internal_core__ops__function__FnMut_trait_type_bounds_definition 4 #1038 #1041
[attach-var-names] #1042 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1043 tr_bound%core!ops.function.Fn. #1023 #264 #45 #46
[mk-app] #1044 and #1035 #1025 #1020
[mk-app] #1045 => #1043 #1044
[mk-app] #1046 pattern #1043
[mk-quant] #1047 internal_core__ops__function__Fn_trait_type_bounds_definition 4 #1046 #1045
[attach-var-names] #1047 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1048 not #1043
[mk-app] #1049 or #1048 #1044
[inst-discovered] theory-solving 0 basic# ; #1045
[mk-app] #1050 = #1045 #1049
[instance] 0 #1050
[attach-enode] #1050 0
[end-of-instance]
[mk-quant] #1050 internal_core__ops__function__Fn_trait_type_bounds_definition 4 #1046 #1049
[attach-var-names] #1050 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1051 tr_bound%core!alloc.Allocator. #45 #46
[mk-app] #1052 pattern #1051
[mk-quant] #1053 internal_core__alloc__Allocator_trait_type_bounds_definition 2 #1052 #1
[attach-var-names] #1053 (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1054 sized #1023
[mk-app] #1055 tr_bound%core!marker.Tuple. #1023 #264
[mk-app] #1056 tr_bound%core!ops.function.Fn. #45 #46 #1023 #264
[mk-app] #1057 and #1054 #1055 #1056
[mk-app] #1058 REF #45
[mk-app] #1059 proj%%core!ops.function.FnOnce./Output #1058 #46 #1023 #264
[mk-app] #1060 proj%%core!ops.function.FnOnce./Output #45 #46 #1023 #264
[mk-app] #1061 = #1059 #1060
[mk-app] #1062 => #1057 #1061
[mk-app] #1063 pattern #1059
[mk-quant] #1064 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 4 #1063 #1062
[attach-var-names] #1064 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1065 not #1057
[mk-app] #1066 or #1065 #1061
[inst-discovered] theory-solving 0 basic# ; #1062
[mk-app] #1067 = #1062 #1066
[instance] 0 #1067
[attach-enode] #1067 0
[end-of-instance]
[mk-quant] #1067 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 4 #1063 #1066
[attach-var-names] #1067 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1068 proj%core!ops.function.FnOnce./Output #1058 #46 #1023 #264
[mk-app] #1069 proj%core!ops.function.FnOnce./Output #45 #46 #1023 #264
[mk-app] #1070 = #1068 #1069
[mk-app] #1071 => #1057 #1070
[mk-app] #1072 pattern #1068
[mk-quant] #1073 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 4 #1072 #1071
[attach-var-names] #1073 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1074 or #1065 #1070
[inst-discovered] theory-solving 0 basic# ; #1071
[mk-app] #1075 = #1071 #1074
[instance] 0 #1075
[attach-enode] #1075 0
[end-of-instance]
[mk-quant] #1075 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 4 #1072 #1074
[attach-var-names] #1075 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1076 tr_bound%core!ops.function.FnMut. #45 #46 #1023 #264
[mk-app] #1077 and #1054 #1055 #1076
[mk-app] #1078 proj%%core!ops.function.FnOnce./Output #121 #47 #1023 #264
[mk-app] #1079 = #1078 #1060
[mk-app] #1080 => #1077 #1079
[mk-app] #1081 pattern #1078
[mk-quant] #1082 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 4 #1081 #1080
[attach-var-names] #1082 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1083 not #1077
[mk-app] #1084 or #1083 #1079
[inst-discovered] theory-solving 0 basic# ; #1080
[mk-app] #1085 = #1080 #1084
[instance] 0 #1085
[attach-enode] #1085 0
[end-of-instance]
[mk-quant] #1085 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 4 #1081 #1084
[attach-var-names] #1085 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1086 proj%core!ops.function.FnOnce./Output #121 #47 #1023 #264
[mk-app] #1087 = #1086 #1069
[mk-app] #1088 => #1077 #1087
[mk-app] #1089 pattern #1086
[mk-quant] #1090 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 4 #1089 #1088
[attach-var-names] #1090 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1091 or #1083 #1087
[inst-discovered] theory-solving 0 basic# ; #1088
[mk-app] #1092 = #1088 #1091
[instance] 0 #1092
[attach-enode] #1092 0
[end-of-instance]
[mk-quant] #1092 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 4 #1089 #1091
[attach-var-names] #1092 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-var] #1093 5
[mk-var] #1094 4
[mk-app] #1095 sized #1093
[mk-app] #1096 tr_bound%core!marker.Tuple. #1093 #1094
[mk-app] #1097 tr_bound%core!ops.function.FnOnce. #1023 #264 #1093 #1094
[mk-app] #1098 and #1095 #1025 #1096 #1097 #1051
[mk-app] #1099 BOX #45 #46 #1023
[mk-app] #1100 proj%%core!ops.function.FnOnce./Output #1099 #264 #1093 #1094
[mk-app] #1101 proj%%core!ops.function.FnOnce./Output #1023 #264 #1093 #1094
[mk-app] #1102 = #1100 #1101
[mk-app] #1103 => #1098 #1102
[mk-app] #1104 pattern #1100
[mk-quant] #1105 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 6 #1104 #1103
[attach-var-names] #1105 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1106 not #1098
[mk-app] #1107 or #1106 #1102
[inst-discovered] theory-solving 0 basic# ; #1103
[mk-app] #1108 = #1103 #1107
[instance] 0 #1108
[attach-enode] #1108 0
[end-of-instance]
[mk-quant] #1108 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 6 #1104 #1107
[attach-var-names] #1108 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1109 proj%core!ops.function.FnOnce./Output #1099 #264 #1093 #1094
[mk-app] #1110 proj%core!ops.function.FnOnce./Output #1023 #264 #1093 #1094
[mk-app] #1111 = #1109 #1110
[mk-app] #1112 => #1098 #1111
[mk-app] #1113 pattern #1109
[mk-quant] #1114 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 6 #1113 #1112
[attach-var-names] #1114 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1115 or #1106 #1111
[inst-discovered] theory-solving 0 basic# ; #1112
[mk-app] #1116 = #1112 #1115
[instance] 0 #1116
[attach-enode] #1116 0
[end-of-instance]
[mk-quant] #1116 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 6 #1113 #1115
[attach-var-names] #1116 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1117 tr_bound%core!ops.function.FnOnce. #121 #47 #1023 #264
[mk-app] #1118 => #1077 #1117
[mk-app] #1119 pattern #1117
[mk-quant] #1120 internal_core__ops__function__impls__impl&__4_trait_impl_definition 4 #1119 #1118
[attach-var-names] #1120 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1121 or #1083 #1117
[inst-discovered] theory-solving 0 basic# ; #1118
[mk-app] #1122 = #1118 #1121
[instance] 0 #1122
[attach-enode] #1122 0
[end-of-instance]
[mk-quant] #1122 internal_core__ops__function__impls__impl&__4_trait_impl_definition 4 #1119 #1121
[attach-var-names] #1122 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1123 fuel_bool #792
[mk-app] #1124 MUTREF #1023 #264
[mk-app] #1125 has_type #33 #1124
[mk-app] #1126 has_type #34 #1094
[mk-app] #1127 and #1125 #1126
[mk-app] #1128 and #1095 #1054
[mk-app] #1129 and #1128 #1096
[mk-app] #1130 tr_bound%core!ops.function.FnMut. #1023 #264 #1093 #1094
[mk-app] #1131 and #1129 #1130
[mk-app] #1132 mut_ref_current% #33
[mk-app] #1133 closure_req #264 #1093 #1094 #1132 #34
[mk-app] #1134 and #1131 #1133
[mk-app] #1135 closure_req #1124 #1093 #1094 #33 #34
[mk-app] #1136 => #1134 #1135
[mk-app] #1137 => #1127 #1136
[mk-app] #1138 pattern #1135
[mk-quant] #1139 user_vstd__function__axiom_fn_mut_call_requires_0 6 #1138 #1137
[attach-var-names] #1139 (|args!| ; |Poly|) (|f!| ; |Poly|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1140 => #1123 #1139
[mk-app] #1141 and #1095 #1054 #1096 #1130 #1133
[mk-app] #1142 not #1141
[mk-app] #1143 or #1142 #1135
[mk-app] #1144 => #1141 #1135
[inst-discovered] theory-solving 0 basic# ; #1144
[mk-app] #1145 = #1144 #1143
[instance] 0 #1145
[attach-enode] #1145 0
[end-of-instance]
[mk-app] #1144 not #1127
[mk-app] #1145 or #1144 #1142 #1135
[mk-app] #1146 => #1127 #1143
[inst-discovered] theory-solving 0 basic# ; #1146
[mk-app] #1147 = #1146 #1145
[instance] 0 #1147
[attach-enode] #1147 0
[end-of-instance]
[mk-quant] #1143 user_vstd__function__axiom_fn_mut_call_requires_0 6 #1138 #1145
[attach-var-names] #1143 (|args!| ; |Poly|) (|f!| ; |Poly|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1146 not #1123
[mk-app] #1147 or #1146 #1143
[mk-app] #1148 => #1123 #1143
[inst-discovered] theory-solving 0 basic# ; #1148
[mk-app] #1149 = #1148 #1147
[instance] 0 #1149
[attach-enode] #1149 0
[end-of-instance]
[mk-app] #1148 fuel_bool #793
[mk-var] #1149 6
[mk-var] #1150 5
[mk-var] #1151 4
[mk-var] #1152 3
[mk-app] #1153 MUTREF #1151 #1152
[mk-app] #1154 has_type #44 #1153
[mk-app] #1155 has_type #33 #1150
[mk-app] #1156 proj%core!ops.function.FnOnce./Output #1151 #1152 #1149 #1150
[mk-app] #1157 has_type #34 #1156
[mk-app] #1158 and #1154 #1155 #1157
[mk-app] #1159 sized #1149
[mk-app] #1160 sized #1151
[mk-app] #1161 and #1159 #1160
[mk-app] #1162 tr_bound%core!marker.Tuple. #1149 #1150
[mk-app] #1163 and #1161 #1162
[mk-app] #1164 tr_bound%core!ops.function.FnMut. #1151 #1152 #1149 #1150
[mk-app] #1165 and #1163 #1164
[mk-app] #1166 closure_ens #1153 #1149 #1150 #44 #33 #34
[mk-app] #1167 and #1165 #1166
[mk-app] #1168 closure_ens #1152 #1149 #1150 #49 #33 #34
[mk-app] #1169 = #49 #57
[mk-app] #1170 and #1168 #1169
[mk-app] #1171 => #1167 #1170
[mk-app] #1172 => #1158 #1171
[mk-app] #1173 pattern #1166
[mk-quant] #1174 user_vstd__function__axiom_fn_mut_call_ensures_1 7 #1173 #1172
[attach-var-names] #1174 (|output!| ; |Poly|) (|args!| ; |Poly|) (|f!| ; |Poly|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1175 => #1148 #1174
[mk-app] #1176 and #1159 #1160 #1162 #1164 #1166
[mk-app] #1177 not #1176
[mk-app] #1178 or #1177 #1170
[mk-app] #1179 => #1176 #1170
[inst-discovered] theory-solving 0 basic# ; #1179
[mk-app] #1180 = #1179 #1178
[instance] 0 #1180
[attach-enode] #1180 0
[end-of-instance]
[mk-app] #1179 not #1158
[mk-app] #1180 or #1179 #1177 #1170
[mk-app] #1181 => #1158 #1178
[inst-discovered] theory-solving 0 basic# ; #1181
[mk-app] #1182 = #1181 #1180
[instance] 0 #1182
[attach-enode] #1182 0
[end-of-instance]
[mk-quant] #1178 user_vstd__function__axiom_fn_mut_call_ensures_1 7 #1173 #1180
[attach-var-names] #1178 (|output!| ; |Poly|) (|args!| ; |Poly|) (|f!| ; |Poly|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1181 not #1148
[mk-app] #1182 or #1181 #1178
[mk-app] #1183 => #1148 #1178
[inst-discovered] theory-solving 0 basic# ; #1183
[mk-app] #1184 = #1183 #1182
[instance] 0 #1184
[attach-enode] #1184 0
[end-of-instance]
[mk-app] #1183 tr_bound%core!marker.Tuple. #121 #1006
[mk-app] #1184 fuel_bool_default #794
[mk-var] #1185 0
[mk-app] #1186 the_q!model.rec%pow2.? #33 #1185
[mk-app] #1187 zero
[mk-app] #1188 the_q!model.rec%pow2.? #33 #1187
[mk-app] #1189 = #1186 #1188
[mk-app] #1190 pattern #1186
[mk-quant] #1191 internal_the_q!model.pow2._fuel_to_zero_definition 2 #1190 #1189
[attach-var-names] #1191 (|fuel%| ; |Fuel|) (|n!| ; |Poly|)
[mk-app] #1192 has_type #33 #196
[mk-app] #1193 succ #1185
[mk-app] #1194 the_q!model.rec%pow2.? #33 #1193
[mk-app] #1195 = #672 #337
[mk-app] #1196 Int
[attach-meaning] #1196 arith 2
[mk-app] #1197 Sub #672 #292
[mk-app] #1198 nClip #1197
[mk-app] #1199 I #1198
[mk-app] #1200 the_q!model.rec%pow2.? #1199 #1185
[mk-app] #1201 Mul #1196 #1200
[mk-app] #1202 if #1195 #292 #1201
[mk-app] #1203 = #1194 #1202
[mk-app] #1204 => #1192 #1203
[mk-app] #1205 pattern #1194
[mk-quant] #1206 internal_the_q!model.pow2._fuel_to_body_definition 2 #1205 #1204
[attach-var-names] #1206 (|fuel%| ; |Fuel|) (|n!| ; |Poly|)
[mk-app] #1207 not #1192
[mk-app] #1208 or #1207 #1203
[inst-discovered] theory-solving 0 basic# ; #1204
[mk-app] #1209 = #1204 #1208
[instance] 0 #1209
[attach-enode] #1209 0
[end-of-instance]
[mk-quant] #1209 internal_the_q!model.pow2._fuel_to_body_definition 2 #1205 #1208
[attach-var-names] #1209 (|fuel%| ; |Fuel|) (|n!| ; |Poly|)
[mk-app] #1210 fuel_bool #794
[mk-app] #1211 the_q!model.pow2.? #34
[mk-app] #1212 fuel_nat%the_q!model.pow2.
[mk-app] #1213 succ #1212
[mk-app] #1214 the_q!model.rec%pow2.? #34 #1213
[mk-app] #1215 = #1211 #1214
[mk-app] #1216 => #197 #1215
[mk-app] #1217 pattern #1211
[mk-quant] #1218 internal_the_q!model.pow2.?_definition 1 #1217 #1216
[attach-var-names] #1218 (|n!| ; |Poly|)
[mk-app] #1219 => #1210 #1218
[mk-app] #1220 or #201 #1215
[inst-discovered] theory-solving 0 basic# ; #1216
[mk-app] #1221 = #1216 #1220
[instance] 0 #1221
[attach-enode] #1221 0
[end-of-instance]
[mk-quant] #1221 internal_the_q!model.pow2.?_definition 1 #1217 #1220
[attach-var-names] #1221 (|n!| ; |Poly|)
[mk-app] #1222 not #1210
[mk-app] #1223 or #1222 #1221
[mk-app] #1224 => #1210 #1221
[inst-discovered] theory-solving 0 basic# ; #1224
[mk-app] #1225 = #1224 #1223
[instance] 0 #1225
[attach-enode] #1225 0
[end-of-instance]
[mk-app] #1224 fuel_bool_default #795
[mk-app] #1225 fuel_bool #795
[mk-app] #1226 the_q!model.abs_int.? #34
[mk-app] #1227 Sub #337 #187
[mk-app] #1228 if #517 #187 #1227
[mk-app] #1229 = #1226 #1228
[mk-app] #1230 pattern #1226
[mk-quant] #1231 internal_the_q!model.abs_int.?_definition 1 #1230 #1229
[attach-var-names] #1231 (|x!| ; |Poly|)
[mk-app] #1232 => #1225 #1231
[mk-app] #1233 not #1225
[mk-app] #1234 or #1233 #1231
[inst-discovered] theory-solving 0 basic# ; #1232
[mk-app] #1235 = #1232 #1234
[instance] 0 #1235
[attach-enode] #1235 0
[end-of-instance]
[mk-app] #1235 fuel_bool_default #796
[mk-app] #1236 fuel_bool #796
[mk-app] #1237 the_q!model.max_int.? #33 #34
[mk-app] #1238 >= #672 #187
[mk-app] #1239 if #1238 #33 #34
[mk-app] #1240 %I #1239
[mk-app] #1241 = #1237 #1240
[mk-app] #1242 pattern #1237
[mk-quant] #1243 internal_the_q!model.max_int.?_definition 2 #1242 #1241
[attach-var-names] #1243 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1244 => #1236 #1243
[attach-meaning] #366 arith (- 1)
[mk-app] #1245 * #366 #187
[mk-app] #1246 + #1245 #672
[attach-meaning] #366 arith (- 1)
[mk-app] #1247 * #366 #672
[mk-app] #1248 + #187 #1247
[mk-app] #1245 <= #1248 #337
[inst-discovered] theory-solving 0 arith# ; #1238
[mk-app] #1246 = #1238 #1245
[instance] 0 #1246
[attach-enode] #1246 0
[end-of-instance]
[mk-app] #1246 if #1245 #33 #34
[mk-app] #1249 %I #1246
[mk-app] #1250 = #1237 #1249
[mk-quant] #1251 internal_the_q!model.max_int.?_definition 2 #1242 #1250
[attach-var-names] #1251 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1252 not #1236
[mk-app] #1253 or #1252 #1251
[mk-app] #1254 => #1236 #1251
[inst-discovered] theory-solving 0 basic# ; #1254
[mk-app] #1255 = #1254 #1253
[instance] 0 #1255
[attach-enode] #1255 0
[end-of-instance]
[mk-app] #1254 fuel_bool_default #797
[mk-app] #1255 fuel_bool #797
[mk-app] #1256 the_q!model.divides.? #33 #34
[mk-app] #1257 Mul #662 #123
[mk-app] #1258 = #672 #1257
[mk-app] #1259 pattern #1257
[mk-quant] #1260 user_the_q__model__divides_2 1 #1259 #1258
[attach-var-names] #1260 (|k$| ; |Int|)
[mk-app] #1261 = #1256 #1260
[mk-app] #1262 pattern #1256
[mk-quant] #1263 internal_the_q!model.divides.?_definition 2 #1262 #1261
[attach-var-names] #1263 (|n!| ; |Poly|) (|d!| ; |Poly|)
[mk-app] #1264 => #1255 #1263
[mk-app] #1265 not #1255
[mk-app] #1266 or #1265 #1263
[inst-discovered] theory-solving 0 basic# ; #1264
[mk-app] #1267 = #1264 #1266
[instance] 0 #1267
[attach-enode] #1267 0
[end-of-instance]
[mk-app] #1267 fuel_bool_default #798
[mk-app] #1268 the_q!model.rec%gcd_nat.? #44 #33 #1185
[mk-app] #1269 the_q!model.rec%gcd_nat.? #44 #33 #1187
[mk-app] #1270 = #1268 #1269
[mk-app] #1271 pattern #1268
[mk-quant] #1272 internal_the_q!model.gcd_nat._fuel_to_zero_definition 3 #1271 #1270
[attach-var-names] #1272 (|fuel%| ; |Fuel|) (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1273 has_type #44 #196
[mk-app] #1274 and #1273 #1192
[mk-app] #1275 the_q!model.rec%gcd_nat.? #44 #33 #1193
[mk-app] #1276 EucMod #662 #672
[mk-app] #1277 I #1276
[mk-app] #1278 the_q!model.rec%gcd_nat.? #33 #1277 #1185
[mk-app] #1279 if #1195 #662 #1278
[mk-app] #1280 = #1275 #1279
[mk-app] #1281 => #1274 #1280
[mk-app] #1282 pattern #1275
[mk-quant] #1283 internal_the_q!model.gcd_nat._fuel_to_body_definition 3 #1282 #1281
[attach-var-names] #1283 (|fuel%| ; |Fuel|) (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1284 not #1274
[mk-app] #1285 or #1284 #1280
[inst-discovered] theory-solving 0 basic# ; #1281
[mk-app] #1286 = #1281 #1285
[instance] 0 #1286
[attach-enode] #1286 0
[end-of-instance]
[mk-quant] #1286 internal_the_q!model.gcd_nat._fuel_to_body_definition 3 #1282 #1285
[attach-var-names] #1286 (|fuel%| ; |Fuel|) (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1287 fuel_bool #798
[mk-app] #1288 and #1192 #197
[mk-app] #1289 the_q!model.gcd_nat.? #33 #34
[mk-app] #1290 fuel_nat%the_q!model.gcd_nat.
[mk-app] #1291 succ #1290
[mk-app] #1292 the_q!model.rec%gcd_nat.? #33 #34 #1291
[mk-app] #1293 = #1289 #1292
[mk-app] #1294 => #1288 #1293
[mk-app] #1295 pattern #1289
[mk-quant] #1296 internal_the_q!model.gcd_nat.?_definition 2 #1295 #1294
[attach-var-names] #1296 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1297 => #1287 #1296
[mk-app] #1298 not #1288
[mk-app] #1299 or #1298 #1293
[inst-discovered] theory-solving 0 basic# ; #1294
[mk-app] #1300 = #1294 #1299
[instance] 0 #1300
[attach-enode] #1300 0
[end-of-instance]
[mk-quant] #1300 internal_the_q!model.gcd_nat.?_definition 2 #1295 #1299
[attach-var-names] #1300 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1301 not #1287
[mk-app] #1302 or #1301 #1300
[mk-app] #1303 => #1287 #1300
[inst-discovered] theory-solving 0 basic# ; #1303
[mk-app] #1304 = #1303 #1302
[instance] 0 #1304
[attach-enode] #1304 0
[end-of-instance]
[mk-app] #1303 <= #337 #1289
[mk-app] #1304 => #1288 #1303
[mk-quant] #1305 internal_the_q!model.gcd_nat.?_pre_post_definition 2 #1295 #1304
[attach-var-names] #1305 (|b!| ; |Poly|) (|a!| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #1306 * #366 #1289
[mk-app] #1307 >= #1289 #337
[inst-discovered] theory-solving 0 arith# ; #1303
[mk-app] #1306 = #1303 #1307
[instance] 0 #1306
[attach-enode] #1306 0
[end-of-instance]
[mk-app] #1306 or #1298 #1307
[mk-app] #1308 => #1288 #1307
[inst-discovered] theory-solving 0 basic# ; #1308
[mk-app] #1309 = #1308 #1306
[instance] 0 #1309
[attach-enode] #1309 0
[end-of-instance]
[mk-quant] #1308 internal_the_q!model.gcd_nat.?_pre_post_definition 2 #1295 #1306
[attach-var-names] #1308 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1309 <= #337 #1268
[mk-app] #1310 => #1274 #1309
[mk-quant] #1311 internal_the_q!model.rec__gcd_nat.?_pre_post_rec_definition 3 #1271 #1310
[attach-var-names] #1311 (|fuel%| ; |Fuel|) (|b!| ; |Poly|) (|a!| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #1312 * #366 #1268
[mk-app] #1313 >= #1268 #337
[inst-discovered] theory-solving 0 arith# ; #1309
[mk-app] #1312 = #1309 #1313
[instance] 0 #1312
[attach-enode] #1312 0
[end-of-instance]
[mk-app] #1312 or #1284 #1313
[mk-app] #1314 => #1274 #1313
[inst-discovered] theory-solving 0 basic# ; #1314
[mk-app] #1315 = #1314 #1312
[instance] 0 #1315
[attach-enode] #1315 0
[end-of-instance]
[mk-quant] #1314 internal_the_q!model.rec__gcd_nat.?_pre_post_rec_definition 3 #1271 #1312
[attach-var-names] #1314 (|fuel%| ; |Fuel|) (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1315 fuel_bool_default #799
[mk-app] #1316 fuel_bool #799
[mk-app] #1317 the_q!model.gcd_int.? #33 #34
[mk-app] #1318 the_q!model.abs_int.? #33
[mk-app] #1319 nClip #1318
[mk-app] #1320 I #1319
[mk-app] #1321 nClip #1226
[mk-app] #1322 I #1321
[mk-app] #1323 the_q!model.gcd_nat.? #1320 #1322
[mk-app] #1324 = #1317 #1323
[mk-app] #1325 pattern #1317
[mk-quant] #1326 internal_the_q!model.gcd_int.?_definition 2 #1325 #1324
[attach-var-names] #1326 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1327 => #1316 #1326
[mk-app] #1328 not #1316
[mk-app] #1329 or #1328 #1326
[inst-discovered] theory-solving 0 basic# ; #1327
[mk-app] #1330 = #1327 #1329
[instance] 0 #1330
[attach-enode] #1330 0
[end-of-instance]
[mk-app] #1330 fuel_bool_default #800
[mk-app] #1331 the_q!model.rec%bitlen.? #33 #1185
[mk-app] #1332 the_q!model.rec%bitlen.? #33 #1187
[mk-app] #1333 = #1331 #1332
[mk-app] #1334 pattern #1331
[mk-quant] #1335 internal_the_q!model.bitlen._fuel_to_zero_definition 2 #1334 #1333
[attach-var-names] #1335 (|fuel%| ; |Fuel|) (|x!| ; |Poly|)
[mk-app] #1336 has_type #33 #185
[mk-app] #1337 the_q!model.rec%bitlen.? #33 #1193
[mk-app] #1338 <= #672 #337
[mk-app] #1339 EucDiv #672 #1196
[mk-app] #1340 I #1339
[mk-app] #1341 the_q!model.rec%bitlen.? #1340 #1185
[mk-app] #1342 Add #1341 #292
[mk-app] #1343 nClip #1342
[mk-app] #1344 if #1338 #337 #1343
[mk-app] #1345 = #1337 #1344
[mk-app] #1346 => #1336 #1345
[mk-app] #1347 pattern #1337
[mk-quant] #1348 internal_the_q!model.bitlen._fuel_to_body_definition 2 #1347 #1346
[attach-var-names] #1348 (|fuel%| ; |Fuel|) (|x!| ; |Poly|)
[mk-app] #1349 not #1336
[mk-app] #1350 or #1349 #1345
[inst-discovered] theory-solving 0 basic# ; #1346
[mk-app] #1351 = #1346 #1350
[instance] 0 #1351
[attach-enode] #1351 0
[end-of-instance]
[mk-quant] #1351 internal_the_q!model.bitlen._fuel_to_body_definition 2 #1347 #1350
[attach-var-names] #1351 (|fuel%| ; |Fuel|) (|x!| ; |Poly|)
[mk-app] #1352 fuel_bool #800
[mk-app] #1353 the_q!model.bitlen.? #34
[mk-app] #1354 fuel_nat%the_q!model.bitlen.
[mk-app] #1355 succ #1354
[mk-app] #1356 the_q!model.rec%bitlen.? #34 #1355
[mk-app] #1357 = #1353 #1356
[mk-app] #1358 => #186 #1357
[mk-app] #1359 pattern #1353
[mk-quant] #1360 internal_the_q!model.bitlen.?_definition 1 #1359 #1358
[attach-var-names] #1360 (|x!| ; |Poly|)
[mk-app] #1361 => #1352 #1360
[mk-app] #1362 or #193 #1357
[inst-discovered] theory-solving 0 basic# ; #1358
[mk-app] #1363 = #1358 #1362
[instance] 0 #1363
[attach-enode] #1363 0
[end-of-instance]
[mk-quant] #1363 internal_the_q!model.bitlen.?_definition 1 #1359 #1362
[attach-var-names] #1363 (|x!| ; |Poly|)
[mk-app] #1364 not #1352
[mk-app] #1365 or #1364 #1363
[mk-app] #1366 => #1352 #1363
[inst-discovered] theory-solving 0 basic# ; #1366
[mk-app] #1367 = #1366 #1365
[instance] 0 #1367
[attach-enode] #1367 0
[end-of-instance]
[mk-app] #1366 <= #337 #1353
[mk-app] #1367 => #186 #1366
[mk-quant] #1368 internal_the_q!model.bitlen.?_pre_post_definition 1 #1359 #1367
[attach-var-names] #1368 (|x!| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #1369 * #366 #1353
[mk-app] #1370 >= #1353 #337
[inst-discovered] theory-solving 0 arith# ; #1366
[mk-app] #1369 = #1366 #1370
[instance] 0 #1369
[attach-enode] #1369 0
[end-of-instance]
[mk-app] #1369 or #193 #1370
[mk-app] #1371 => #186 #1370
[inst-discovered] theory-solving 0 basic# ; #1371
[mk-app] #1372 = #1371 #1369
[instance] 0 #1372
[attach-enode] #1372 0
[end-of-instance]
[mk-quant] #1371 internal_the_q!model.bitlen.?_pre_post_definition 1 #1359 #1369
[attach-var-names] #1371 (|x!| ; |Poly|)
[mk-app] #1372 <= #337 #1331
[mk-app] #1373 => #1336 #1372
[mk-quant] #1374 internal_the_q!model.rec__bitlen.?_pre_post_rec_definition 2 #1334 #1373
[attach-var-names] #1374 (|fuel%| ; |Fuel|) (|x!| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #1375 * #366 #1331
[mk-app] #1376 >= #1331 #337
[inst-discovered] theory-solving 0 arith# ; #1372
[mk-app] #1375 = #1372 #1376
[instance] 0 #1375
[attach-enode] #1375 0
[end-of-instance]
[mk-app] #1375 or #1349 #1376
[mk-app] #1377 => #1336 #1376
[inst-discovered] theory-solving 0 basic# ; #1377
[mk-app] #1378 = #1377 #1375
[instance] 0 #1378
[attach-enode] #1378 0
[end-of-instance]
[mk-quant] #1377 internal_the_q!model.rec__bitlen.?_pre_post_rec_definition 2 #1334 #1375
[attach-var-names] #1377 (|fuel%| ; |Fuel|) (|x!| ; |Poly|)
[mk-app] #1378 fuel_bool_default #817
[mk-app] #1379 fuel_bool #817
[mk-app] #1380 the_q!types.MAX_MAG.?
[mk-app] #1381 Int
[attach-meaning] #1381 arith 4611686018427387903
[mk-app] #1382 = #1380 #1381
[mk-app] #1383 => #1379 #1382
[mk-app] #1384 not #1379
[mk-app] #1385 or #1384 #1382
[inst-discovered] theory-solving 0 basic# ; #1383
[mk-app] #1386 = #1383 #1385
[instance] 0 #1386
[attach-enode] #1386 0
[end-of-instance]
[attach-meaning] #273 arith 64
[mk-app] #1386 iInv #273 #1380
[mk-app] #1387 fuel_bool_default #801
[mk-app] #1388 fuel_bool #801
[mk-app] #1389 the_q!model.max_mag.? #34
[mk-app] #1390 = #1389 #1380
[mk-app] #1391 pattern #1389
[mk-quant] #1392 internal_the_q!model.max_mag.?_definition 1 #1391 #1390
[attach-var-names] #1392 (|no%param| ; |Poly|)
[mk-app] #1393 => #1388 #1392
[mk-app] #1394 not #1388
[mk-app] #1395 or #1394 #1392
[inst-discovered] theory-solving 0 basic# ; #1393
[mk-app] #1396 = #1393 #1395
[instance] 0 #1396
[attach-enode] #1396 0
[end-of-instance]
[mk-app] #1396 fuel_bool_default #802
[mk-app] #1397 fuel_bool #802
[mk-app] #1398 the_q!model.fits_budget.? #33 #34
[mk-app] #1399 I #337
[mk-app] #1400 the_q!model.max_mag.? #1399
[mk-app] #1401 <= #1318 #1400
[mk-app] #1402 <= #187 #1400
[mk-app] #1403 and #1401 #1402
[mk-app] #1404 = #1398 #1403
[mk-app] #1405 pattern #1398
[mk-quant] #1406 internal_the_q!model.fits_budget.?_definition 2 #1405 #1404
[attach-var-names] #1406 (|d!| ; |Poly|) (|n!| ; |Poly|)
[mk-app] #1407 => #1397 #1406
[attach-meaning] #366 arith (- 1)
[mk-app] #1408 * #366 #1400
[mk-app] #1409 + #1318 #1408
[mk-app] #1410 <= #1409 #337
[inst-discovered] theory-solving 0 arith# ; #1401
[mk-app] #1411 = #1401 #1410
[instance] 0 #1411
[attach-enode] #1411 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #1411 + #187 #1408
[mk-app] #1412 <= #1411 #337
[inst-discovered] theory-solving 0 arith# ; #1402
[mk-app] #1413 = #1402 #1412
[instance] 0 #1413
[attach-enode] #1413 0
[end-of-instance]
[mk-app] #1413 and #1410 #1412
[mk-app] #1414 = #1398 #1413
[mk-quant] #1415 internal_the_q!model.fits_budget.?_definition 2 #1405 #1414
[attach-var-names] #1415 (|d!| ; |Poly|) (|n!| ; |Poly|)
[mk-app] #1416 not #1397
[mk-app] #1417 or #1416 #1415
[mk-app] #1418 => #1397 #1415
[inst-discovered] theory-solving 0 basic# ; #1418
[mk-app] #1419 = #1418 #1417
[instance] 0 #1419
[attach-enode] #1419 0
[end-of-instance]
[mk-app] #1418 fuel_bool_default #803
[mk-app] #1419 fuel_bool #803
[mk-app] #1420 the_q!model.magnitude_fits.? #33 #34
[mk-app] #1421 Mul #1400 #187
[mk-app] #1422 <= #1318 #1421
[mk-app] #1423 = #1420 #1422
[mk-app] #1424 pattern #1420
[mk-quant] #1425 internal_the_q!model.magnitude_fits.?_definition 2 #1424 #1423
[attach-var-names] #1425 (|d!| ; |Poly|) (|n!| ; |Poly|)
[mk-app] #1426 => #1419 #1425
[attach-meaning] #366 arith (- 1)
[mk-app] #1427 * #366 #1421
[mk-app] #1428 + #1318 #1427
[mk-app] #1429 <= #1428 #337
[inst-discovered] theory-solving 0 arith# ; #1422
[mk-app] #1430 = #1422 #1429
[instance] 0 #1430
[attach-enode] #1430 0
[end-of-instance]
[mk-app] #1430 = #1420 #1429
[mk-quant] #1431 internal_the_q!model.magnitude_fits.?_definition 2 #1424 #1430
[attach-var-names] #1431 (|d!| ; |Poly|) (|n!| ; |Poly|)
[mk-app] #1432 not #1419
[mk-app] #1433 or #1432 #1431
[mk-app] #1434 => #1419 #1431
[inst-discovered] theory-solving 0 basic# ; #1434
[mk-app] #1435 = #1434 #1433
[instance] 0 #1435
[attach-enode] #1435 0
[end-of-instance]
[mk-app] #1434 fuel_bool_default #804
[mk-app] #1435 fuel_bool #804
[mk-app] #1436 the_q!model.impl&%0.wf.? #34
[mk-app] #1437 > #993 #337
[mk-app] #1438 I #981
[mk-app] #1439 I #993
[mk-app] #1440 the_q!model.gcd_int.? #1438 #1439
[mk-app] #1441 = #1440 #292
[mk-app] #1442 and #1437 #1441
[mk-app] #1443 = #981 #337
[mk-app] #1444 = #993 #292
[mk-app] #1445 => #1443 #1444
[mk-app] #1446 and #1442 #1445
[mk-app] #1447 the_q!model.abs_int.? #1438
[mk-app] #1448 <= #1447 #1400
[mk-app] #1449 and #1446 #1448
[mk-app] #1450 <= #993 #1400
[mk-app] #1451 and #1449 #1450
[mk-app] #1452 = #1436 #1451
[mk-app] #1453 pattern #1436
[mk-quant] #1454 internal_the_q!model.impl&__0.wf.?_definition 1 #1453 #1452
[attach-var-names] #1454 (|self!| ; |Poly|)
[mk-app] #1455 => #1435 #1454
[mk-app] #1456 <= #993 #337
[mk-app] #1457 not #1456
[inst-discovered] theory-solving 0 arith# ; #1437
[mk-app] #1458 = #1437 #1457
[instance] 0 #1458
[attach-enode] #1458 0
[end-of-instance]
[mk-app] #1458 not #1443
[mk-app] #1459 or #1458 #1444
[inst-discovered] theory-solving 0 basic# ; #1445
[mk-app] #1460 = #1445 #1459
[instance] 0 #1460
[attach-enode] #1460 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #1460 + #1408 #1447
[attach-meaning] #366 arith (- 1)
[mk-app] #1461 * #366 #1447
[mk-app] #1462 + #1400 #1461
[mk-app] #1460 >= #1462 #337
[inst-discovered] theory-solving 0 arith# ; #1448
[mk-app] #1463 = #1448 #1460
[instance] 0 #1463
[attach-enode] #1463 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #1463 + #993 #1408
[mk-app] #1464 <= #1463 #337
[inst-discovered] theory-solving 0 arith# ; #1450
[mk-app] #1465 = #1450 #1464
[instance] 0 #1465
[attach-enode] #1465 0
[end-of-instance]
[mk-app] #1465 and #1457 #1441 #1459 #1460 #1464
[mk-app] #1466 = #1436 #1465
[mk-quant] #1467 internal_the_q!model.impl&__0.wf.?_definition 1 #1453 #1466
[attach-var-names] #1467 (|self!| ; |Poly|)
[mk-app] #1468 not #1435
[mk-app] #1469 or #1468 #1467
[mk-app] #1470 => #1435 #1467
[inst-discovered] theory-solving 0 basic# ; #1470
[mk-app] #1471 = #1470 #1469
[instance] 0 #1471
[attach-enode] #1471 0
[end-of-instance]
[mk-app] #1470 fuel_bool_default #805
[mk-app] #1471 fuel_bool #805
[mk-app] #1472 the_q!model.impl&%0.n.? #34
[mk-app] #1473 = #1472 #981
[mk-app] #1474 pattern #1472
[mk-quant] #1475 internal_the_q!model.impl&__0.n.?_definition 1 #1474 #1473
[attach-var-names] #1475 (|self!| ; |Poly|)
[mk-app] #1476 => #1471 #1475
[mk-app] #1477 not #1471
[mk-app] #1478 or #1477 #1475
[inst-discovered] theory-solving 0 basic# ; #1476
[mk-app] #1479 = #1476 #1478
[instance] 0 #1479
[attach-enode] #1479 0
[end-of-instance]
[mk-app] #1479 fuel_bool_default #806
[mk-app] #1480 fuel_bool #806
[mk-app] #1481 the_q!model.impl&%0.d.? #34
[mk-app] #1482 = #1481 #993
[mk-app] #1483 pattern #1481
[mk-quant] #1484 internal_the_q!model.impl&__0.d.?_definition 1 #1483 #1482
[attach-var-names] #1484 (|self!| ; |Poly|)
[mk-app] #1485 => #1480 #1484
[mk-app] #1486 not #1480
[mk-app] #1487 or #1486 #1484
[inst-discovered] theory-solving 0 basic# ; #1485
[mk-app] #1488 = #1485 #1487
[instance] 0 #1488
[attach-enode] #1488 0
[end-of-instance]
[mk-app] #1488 fuel_bool_default #807
[mk-app] #1489 fuel_bool #807
[mk-app] #1490 the_q!model.q_eq.? #33 #34
[mk-app] #1491 the_q!model.impl&%0.n.? #33
[mk-app] #1492 Mul #1491 #1481
[mk-app] #1493 the_q!model.impl&%0.d.? #33
[mk-app] #1494 Mul #1472 #1493
[mk-app] #1495 = #1492 #1494
[mk-app] #1496 = #1490 #1495
[mk-app] #1497 pattern #1490
[mk-quant] #1498 internal_the_q!model.q_eq.?_definition 2 #1497 #1496
[attach-var-names] #1498 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1499 => #1489 #1498
[mk-app] #1500 not #1489
[mk-app] #1501 or #1500 #1498
[inst-discovered] theory-solving 0 basic# ; #1499
[mk-app] #1502 = #1499 #1501
[instance] 0 #1502
[attach-enode] #1502 0
[end-of-instance]
[mk-app] #1502 fuel_bool_default #808
[mk-app] #1503 fuel_bool #808
[mk-app] #1504 the_q!model.q_le.? #33 #34
[mk-app] #1505 <= #1492 #1494
[mk-app] #1506 = #1504 #1505
[mk-app] #1507 pattern #1504
[mk-quant] #1508 internal_the_q!model.q_le.?_definition 2 #1507 #1506
[attach-var-names] #1508 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1509 => #1503 #1508
[attach-meaning] #366 arith (- 1)
[mk-app] #1510 * #366 #1494
[mk-app] #1511 + #1492 #1510
[mk-app] #1512 <= #1511 #337
[inst-discovered] theory-solving 0 arith# ; #1505
[mk-app] #1513 = #1505 #1512
[instance] 0 #1513
[attach-enode] #1513 0
[end-of-instance]
[mk-app] #1513 = #1504 #1512
[mk-quant] #1514 internal_the_q!model.q_le.?_definition 2 #1507 #1513
[attach-var-names] #1514 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1515 not #1503
[mk-app] #1516 or #1515 #1514
[mk-app] #1517 => #1503 #1514
[inst-discovered] theory-solving 0 basic# ; #1517
[mk-app] #1518 = #1517 #1516
[instance] 0 #1518
[attach-enode] #1518 0
[end-of-instance]
[mk-app] #1517 fuel_bool_default #809
[mk-app] #1518 fuel_bool #809
[mk-app] #1519 the_q!model.q_lt.? #33 #34
[mk-app] #1520 < #1492 #1494
[mk-app] #1521 = #1519 #1520
[mk-app] #1522 pattern #1519
[mk-quant] #1523 internal_the_q!model.q_lt.?_definition 2 #1522 #1521
[attach-var-names] #1523 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1524 => #1518 #1523
[mk-app] #1525 <= #1494 #1492
[mk-app] #1526 not #1525
[inst-discovered] theory-solving 0 arith# ; #1520
[mk-app] #1527 = #1520 #1526
[instance] 0 #1527
[attach-enode] #1527 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #1527 * #366 #1492
[mk-app] #1528 + #1527 #1494
[attach-meaning] #366 arith (- 1)
[mk-app] #1527 >= #1511 #337
[inst-discovered] theory-solving 0 arith# ; #1525
[mk-app] #1528 = #1525 #1527
[instance] 0 #1528
[attach-enode] #1528 0
[end-of-instance]
[mk-app] #1528 not #1527
[mk-app] #1529 = #1527 #1519
[mk-app] #1530 not #1529
[mk-app] #1531 = #1519 #1528
[inst-discovered] theory-solving 0 basic# ; #1531
[mk-app] #1532 = #1531 #1530
[instance] 0 #1532
[attach-enode] #1532 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #1531 = #1530 #1530
[instance] 0 #1531
[attach-enode] #1531 0
[end-of-instance]
[mk-quant] #1531 internal_the_q!model.q_lt.?_definition 2 #1522 #1530
[attach-var-names] #1531 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #1528 not #1518
[mk-app] #1525 or #1528 #1531
[mk-app] #1526 => #1518 #1531
[inst-discovered] theory-solving 0 basic# ; #1526
[mk-app] #1532 = #1526 #1525
[instance] 0 #1532
[attach-enode] #1532 0
[end-of-instance]
[mk-app] #1526 fuel_bool_default #810
[mk-app] #1532 fuel_bool #810
[mk-app] #1533 the_q!model.q_is.? #44 #33 #34
[mk-app] #1534 the_q!model.impl&%0.n.? #44
[mk-app] #1535 Mul #1534 #187
[mk-app] #1536 the_q!model.impl&%0.d.? #44
[mk-app] #1537 Mul #672 #1536
[mk-app] #1538 = #1535 #1537
[mk-app] #1539 = #1533 #1538
[mk-app] #1540 pattern #1533
[mk-quant] #1541 internal_the_q!model.q_is.?_definition 3 #1540 #1539
[attach-var-names] #1541 (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1542 => #1532 #1541
[mk-app] #1543 not #1532
[mk-app] #1544 or #1543 #1541
[inst-discovered] theory-solving 0 basic# ; #1542
[mk-app] #1545 = #1542 #1544
[instance] 0 #1545
[attach-enode] #1545 0
[end-of-instance]
[mk-app] #1545 fuel_bool_default #811
[mk-app] #1546 fuel_bool #811
[mk-app] #1547 the_q!model.q_le_frac.? #44 #33 #34
[mk-app] #1548 <= #1535 #1537
[mk-app] #1549 = #1547 #1548
[mk-app] #1550 pattern #1547
[mk-quant] #1551 internal_the_q!model.q_le_frac.?_definition 3 #1550 #1549
[attach-var-names] #1551 (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1552 => #1546 #1551
[attach-meaning] #366 arith (- 1)
[mk-app] #1553 * #366 #1537
[mk-app] #1554 + #1535 #1553
[mk-app] #1555 <= #1554 #337
[inst-discovered] theory-solving 0 arith# ; #1548
[mk-app] #1556 = #1548 #1555
[instance] 0 #1556
[attach-enode] #1556 0
[end-of-instance]
[mk-app] #1556 = #1547 #1555
[mk-quant] #1557 internal_the_q!model.q_le_frac.?_definition 3 #1550 #1556
[attach-var-names] #1557 (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1558 not #1546
[mk-app] #1559 or #1558 #1557
[mk-app] #1560 => #1546 #1557
[inst-discovered] theory-solving 0 basic# ; #1560
[mk-app] #1561 = #1560 #1559
[instance] 0 #1561
[attach-enode] #1561 0
[end-of-instance]
[mk-app] #1560 fuel_bool_default #812
[mk-app] #1561 fuel_bool #812
[mk-app] #1562 the_q!model.q_ge_frac.? #44 #33 #34
[mk-app] #1563 >= #1535 #1537
[mk-app] #1564 = #1562 #1563
[mk-app] #1565 pattern #1562
[mk-quant] #1566 internal_the_q!model.q_ge_frac.?_definition 3 #1565 #1564
[attach-var-names] #1566 (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1567 => #1561 #1566
[attach-meaning] #366 arith (- 1)
[mk-app] #1568 >= #1554 #337
[inst-discovered] theory-solving 0 arith# ; #1563
[mk-app] #1569 = #1563 #1568
[instance] 0 #1569
[attach-enode] #1569 0
[end-of-instance]
[mk-app] #1569 = #1562 #1568
[mk-quant] #1570 internal_the_q!model.q_ge_frac.?_definition 3 #1565 #1569
[attach-var-names] #1570 (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1571 not #1561
[mk-app] #1572 or #1571 #1570
[mk-app] #1573 => #1561 #1570
[inst-discovered] theory-solving 0 basic# ; #1573
[mk-app] #1574 = #1573 #1572
[instance] 0 #1574
[attach-enode] #1574 0
[end-of-instance]
[mk-app] #1573 fuel_bool_default #813
[mk-app] #1574 fuel_bool #813
[mk-app] #1575 the_q!model.precision_b.? #34
[mk-app] #1576 Int
[attach-meaning] #1576 arith 61
[mk-app] #1577 = #1575 #1576
[mk-app] #1578 pattern #1575
[mk-quant] #1579 internal_the_q!model.precision_b.?_definition 1 #1578 #1577
[attach-var-names] #1579 (|no%param| ; |Poly|)
[mk-app] #1580 => #1574 #1579
[mk-app] #1581 not #1574
[mk-app] #1582 or #1581 #1579
[inst-discovered] theory-solving 0 basic# ; #1580
[mk-app] #1583 = #1580 #1582
[instance] 0 #1583
[attach-enode] #1583 0
[end-of-instance]
[mk-app] #1583 <= #337 #1575
[mk-app] #1584 => #186 #1583
[mk-quant] #1585 internal_the_q!model.precision_b.?_pre_post_definition 1 #1578 #1584
[attach-var-names] #1585 (|no%param| ; |Poly|)
[attach-meaning] #366 arith (- 1)
[mk-app] #1586 * #366 #1575
[mk-app] #1587 >= #1575 #337
[inst-discovered] theory-solving 0 arith# ; #1583
[mk-app] #1586 = #1583 #1587
[instance] 0 #1586
[attach-enode] #1586 0
[end-of-instance]
[mk-app] #1586 or #193 #1587
[mk-app] #1588 => #186 #1587
[inst-discovered] theory-solving 0 basic# ; #1588
[mk-app] #1589 = #1588 #1586
[instance] 0 #1589
[attach-enode] #1589 0
[end-of-instance]
[mk-quant] #1588 internal_the_q!model.precision_b.?_pre_post_definition 1 #1578 #1586
[attach-var-names] #1588 (|no%param| ; |Poly|)
[mk-app] #1589 fuel_bool_default #814
[mk-app] #1590 fuel_bool #814
[mk-app] #1591 the_q!model.within_error_bound.? #44 #33 #34
[mk-app] #1592 Sub #1535 #1537
[mk-app] #1593 I #1592
[mk-app] #1594 the_q!model.abs_int.? #1593
[mk-app] #1595 the_q!model.precision_b.? #1399
[mk-app] #1596 I #1595
[mk-app] #1597 the_q!model.pow2.? #1596
[mk-app] #1598 Mul #1594 #1597
[mk-app] #1599 I #1318
[mk-app] #1600 the_q!model.max_int.? #34 #1599
[mk-app] #1601 Mul #1536 #1600
[mk-app] #1602 <= #1598 #1601
[mk-app] #1603 = #1591 #1602
[mk-app] #1604 pattern #1591
[mk-quant] #1605 internal_the_q!model.within_error_bound.?_definition 3 #1604 #1603
[attach-var-names] #1605 (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1606 => #1590 #1605
[attach-meaning] #366 arith (- 1)
[mk-app] #1607 * #366 #1601
[mk-app] #1608 + #1598 #1607
[mk-app] #1609 <= #1608 #337
[inst-discovered] theory-solving 0 arith# ; #1602
[mk-app] #1610 = #1602 #1609
[instance] 0 #1610
[attach-enode] #1610 0
[end-of-instance]
[mk-app] #1610 = #1591 #1609
[mk-quant] #1611 internal_the_q!model.within_error_bound.?_definition 3 #1604 #1610
[attach-var-names] #1611 (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1612 not #1590
[mk-app] #1613 or #1612 #1611
[mk-app] #1614 => #1590 #1611
[inst-discovered] theory-solving 0 basic# ; #1614
[mk-app] #1615 = #1614 #1613
[instance] 0 #1615
[attach-enode] #1615 0
[end-of-instance]
[mk-app] #1614 fuel_bool_default #815
[mk-app] #1615 fuel_bool #815
[mk-app] #1616 the_q!model.within_error_bound_k.? #64 #44 #33 #34
[mk-app] #1617 the_q!model.impl&%0.n.? #64
[mk-app] #1618 Mul #1617 #672
[mk-app] #1619 the_q!model.impl&%0.d.? #64
[mk-app] #1620 Mul #662 #1619
[mk-app] #1621 Sub #1618 #1620
[mk-app] #1622 I #1621
[mk-app] #1623 the_q!model.abs_int.? #1622
[mk-app] #1624 Mul #1623 #1597
[mk-app] #1625 Mul #187 #1619
[mk-app] #1626 the_q!model.abs_int.? #44
[mk-app] #1627 I #1626
[mk-app] #1628 the_q!model.max_int.? #33 #1627
[mk-app] #1629 Mul #1625 #1628
[mk-app] #1630 <= #1624 #1629
[mk-app] #1631 = #1616 #1630
[mk-app] #1632 pattern #1616
[mk-quant] #1633 internal_the_q!model.within_error_bound_k.?_definition 4 #1632 #1631
[attach-var-names] #1633 (|k!| ; |Poly|) (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1634 => #1615 #1633
[attach-meaning] #366 arith (- 1)
[mk-app] #1635 * #366 #1629
[mk-app] #1636 + #1624 #1635
[mk-app] #1637 <= #1636 #337
[inst-discovered] theory-solving 0 arith# ; #1630
[mk-app] #1638 = #1630 #1637
[instance] 0 #1638
[attach-enode] #1638 0
[end-of-instance]
[mk-app] #1638 = #1616 #1637
[mk-quant] #1639 internal_the_q!model.within_error_bound_k.?_definition 4 #1632 #1638
[attach-var-names] #1639 (|k!| ; |Poly|) (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1640 not #1615
[mk-app] #1641 or #1640 #1639
[mk-app] #1642 => #1615 #1639
[inst-discovered] theory-solving 0 basic# ; #1642
[mk-app] #1643 = #1642 #1641
[instance] 0 #1643
[attach-enode] #1643 0
[end-of-instance]
[mk-app] #1642 fuel_bool_default #816
[mk-app] #1643 fuel_bool #816
[mk-var] #1644 4
[mk-app] #1645 the_q!model.within_abs_error.? #1644 #64 #44 #33 #34
[mk-app] #1646 the_q!model.impl&%0.n.? #1644
[mk-app] #1647 Mul #1646 #662
[mk-app] #1648 %I #64
[mk-app] #1649 the_q!model.impl&%0.d.? #1644
[mk-app] #1650 Mul #1648 #1649
[mk-app] #1651 Sub #1647 #1650
[mk-app] #1652 I #1651
[mk-app] #1653 the_q!model.abs_int.? #1652
[mk-app] #1654 Mul #1653 #1597
[mk-app] #1655 Mul #672 #187
[mk-app] #1656 Mul #1649 #662
[mk-app] #1657 Mul #1655 #1656
[mk-app] #1658 <= #1654 #1657
[mk-app] #1659 = #1645 #1658
[mk-app] #1660 pattern #1645
[mk-quant] #1661 internal_the_q!model.within_abs_error.?_definition 5 #1660 #1659
[attach-var-names] #1661 (|m!| ; |Poly|) (|k!| ; |Poly|) (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1662 => #1643 #1661
[attach-meaning] #366 arith (- 1)
[mk-app] #1663 * #366 #1657
[mk-app] #1664 + #1654 #1663
[mk-app] #1665 <= #1664 #337
[inst-discovered] theory-solving 0 arith# ; #1658
[mk-app] #1666 = #1658 #1665
[instance] 0 #1666
[attach-enode] #1666 0
[end-of-instance]
[mk-app] #1666 = #1645 #1665
[mk-quant] #1667 internal_the_q!model.within_abs_error.?_definition 5 #1660 #1666
[attach-var-names] #1667 (|m!| ; |Poly|) (|k!| ; |Poly|) (|d!| ; |Poly|) (|n!| ; |Poly|) (|r!| ; |Poly|)
[mk-app] #1668 not #1643
[mk-app] #1669 or #1668 #1667
[mk-app] #1670 => #1643 #1667
[inst-discovered] theory-solving 0 basic# ; #1670
[mk-app] #1671 = #1670 #1669
[instance] 0 #1671
[attach-enode] #1671 0
[end-of-instance]
[mk-app] #1670 tr_bound%core!ops.function.FnOnce. #1058 #46 #1023 #264
[mk-app] #1671 => #1057 #1670
[mk-app] #1672 pattern #1670
[mk-quant] #1673 internal_core__ops__function__impls__impl&__2_trait_impl_definition 4 #1672 #1671
[attach-var-names] #1673 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1674 or #1065 #1670
[inst-discovered] theory-solving 0 basic# ; #1671
[mk-app] #1675 = #1671 #1674
[instance] 0 #1675
[attach-enode] #1675 0
[end-of-instance]
[mk-quant] #1675 internal_core__ops__function__impls__impl&__2_trait_impl_definition 4 #1672 #1674
[attach-var-names] #1675 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1676 tr_bound%core!ops.function.FnMut. #1058 #46 #1023 #264
[mk-app] #1677 => #1057 #1676
[mk-app] #1678 pattern #1676
[mk-quant] #1679 internal_core__ops__function__impls__impl&__1_trait_impl_definition 4 #1678 #1677
[attach-var-names] #1679 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1680 or #1065 #1676
[inst-discovered] theory-solving 0 basic# ; #1677
[mk-app] #1681 = #1677 #1680
[instance] 0 #1681
[attach-enode] #1681 0
[end-of-instance]
[mk-quant] #1681 internal_core__ops__function__impls__impl&__1_trait_impl_definition 4 #1678 #1680
[attach-var-names] #1681 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1682 tr_bound%core!ops.function.Fn. #1058 #46 #1023 #264
[mk-app] #1683 => #1057 #1682
[mk-app] #1684 pattern #1682
[mk-quant] #1685 internal_core__ops__function__impls__impl&__0_trait_impl_definition 4 #1684 #1683
[attach-var-names] #1685 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1686 or #1065 #1682
[inst-discovered] theory-solving 0 basic# ; #1683
[mk-app] #1687 = #1683 #1686
[instance] 0 #1687
[attach-enode] #1687 0
[end-of-instance]
[mk-quant] #1687 internal_core__ops__function__impls__impl&__0_trait_impl_definition 4 #1684 #1686
[attach-var-names] #1687 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1688 tr_bound%core!ops.function.FnOnce. #1099 #264 #1093 #1094
[mk-app] #1689 => #1098 #1688
[mk-app] #1690 pattern #1688
[mk-quant] #1691 internal_alloc__boxed__impl&__31_trait_impl_definition 6 #1690 #1689
[attach-var-names] #1691 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1692 or #1106 #1688
[inst-discovered] theory-solving 0 basic# ; #1689
[mk-app] #1693 = #1689 #1692
[instance] 0 #1693
[attach-enode] #1693 0
[end-of-instance]
[mk-quant] #1693 internal_alloc__boxed__impl&__31_trait_impl_definition 6 #1690 #1692
[attach-var-names] #1693 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1694 and #1095 #1025 #1096 #1130 #1051
[mk-app] #1695 tr_bound%core!ops.function.FnMut. #1099 #264 #1093 #1094
[mk-app] #1696 => #1694 #1695
[mk-app] #1697 pattern #1695
[mk-quant] #1698 internal_alloc__boxed__impl&__32_trait_impl_definition 6 #1697 #1696
[attach-var-names] #1698 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1699 not #1694
[mk-app] #1700 or #1699 #1695
[inst-discovered] theory-solving 0 basic# ; #1696
[mk-app] #1701 = #1696 #1700
[instance] 0 #1701
[attach-enode] #1701 0
[end-of-instance]
[mk-quant] #1701 internal_alloc__boxed__impl&__32_trait_impl_definition 6 #1697 #1700
[attach-var-names] #1701 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1702 tr_bound%core!ops.function.Fn. #1023 #264 #1093 #1094
[mk-app] #1703 and #1095 #1025 #1096 #1702 #1051
[mk-app] #1704 tr_bound%core!ops.function.Fn. #1099 #264 #1093 #1094
[mk-app] #1705 => #1703 #1704
[mk-app] #1706 pattern #1704
[mk-quant] #1707 internal_alloc__boxed__impl&__33_trait_impl_definition 6 #1706 #1705
[attach-var-names] #1707 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1708 not #1703
[mk-app] #1709 or #1708 #1704
[inst-discovered] theory-solving 0 basic# ; #1705
[mk-app] #1710 = #1705 #1709
[instance] 0 #1710
[attach-enode] #1710 0
[end-of-instance]
[mk-quant] #1710 internal_alloc__boxed__impl&__33_trait_impl_definition 6 #1706 #1709
[attach-var-names] #1710 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1711 tr_bound%core!ops.function.FnMut. #121 #47 #1023 #264
[mk-app] #1712 => #1077 #1711
[mk-app] #1713 pattern #1711
[mk-quant] #1714 internal_core__ops__function__impls__impl&__3_trait_impl_definition 4 #1713 #1712
[attach-var-names] #1714 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1715 or #1083 #1711
[inst-discovered] theory-solving 0 basic# ; #1712
[mk-app] #1716 = #1712 #1715
[instance] 0 #1716
[attach-enode] #1716 0
[end-of-instance]
[mk-quant] #1716 internal_core__ops__function__impls__impl&__3_trait_impl_definition 4 #1713 #1715
[attach-var-names] #1716 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1717 tr_bound%core!alloc.Allocator. #1058 #46
[mk-app] #1718 => #1051 #1717
[mk-app] #1719 pattern #1717
[mk-quant] #1720 internal_core__alloc__impl&__2_trait_impl_definition 2 #1719 #1718
[attach-var-names] #1720 (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1721 not #1051
[mk-app] #1722 or #1721 #1717
[inst-discovered] theory-solving 0 basic# ; #1718
[mk-app] #1723 = #1718 #1722
[instance] 0 #1723
[attach-enode] #1723 0
[end-of-instance]
[mk-quant] #1723 internal_core__alloc__impl&__2_trait_impl_definition 2 #1719 #1722
[attach-var-names] #1723 (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1724 tr_bound%core!alloc.Allocator. #121 #47
[mk-app] #1725 => #1051 #1724
[mk-app] #1726 pattern #1724
[mk-quant] #1727 internal_core__alloc__impl&__3_trait_impl_definition 2 #1726 #1725
[attach-var-names] #1727 (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1728 or #1721 #1724
[inst-discovered] theory-solving 0 basic# ; #1725
[mk-app] #1729 = #1725 #1728
[instance] 0 #1729
[attach-enode] #1729 0
[end-of-instance]
[mk-quant] #1729 internal_core__alloc__impl&__3_trait_impl_definition 2 #1726 #1728
[attach-var-names] #1729 (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1730 tr_bound%core!alloc.Allocator. #1023 #264
[mk-app] #1731 and #1025 #1730 #1051
[mk-app] #1732 tr_bound%core!alloc.Allocator. #1099 #264
[mk-app] #1733 => #1731 #1732
[mk-app] #1734 pattern #1732
[mk-quant] #1735 internal_alloc__boxed__impl&__49_trait_impl_definition 4 #1734 #1733
[attach-var-names] #1735 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #1736 not #1731
[mk-app] #1737 or #1736 #1732
[inst-discovered] theory-solving 0 basic# ; #1733
[mk-app] #1738 = #1733 #1737
[instance] 0 #1738
[attach-enode] #1738 0
[end-of-instance]
[mk-quant] #1738 internal_alloc__boxed__impl&__49_trait_impl_definition 4 #1734 #1737
[attach-var-names] #1738 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #1739 RC #45 #46 #1023
[mk-app] #1740 tr_bound%core!alloc.Allocator. #1739 #264
[mk-app] #1741 => #1731 #1740
[mk-app] #1742 pattern #1740
[mk-quant] #1743 internal_alloc__rc__impl&__115_trait_impl_definition 4 #1742 #1741
[attach-var-names] #1743 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #1744 or #1736 #1740
[inst-discovered] theory-solving 0 basic# ; #1741
[mk-app] #1745 = #1741 #1744
[instance] 0 #1745
[attach-enode] #1745 0
[end-of-instance]
[mk-quant] #1745 internal_alloc__rc__impl&__115_trait_impl_definition 4 #1742 #1744
[attach-var-names] #1745 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #1746 ARC #45 #46 #1023
[mk-app] #1747 tr_bound%core!alloc.Allocator. #1746 #264
[mk-app] #1748 => #1731 #1747
[mk-app] #1749 pattern #1747
[mk-quant] #1750 internal_alloc__sync__impl&__117_trait_impl_definition 4 #1749 #1748
[attach-var-names] #1750 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #1751 or #1736 #1747
[inst-discovered] theory-solving 0 basic# ; #1748
[mk-app] #1752 = #1748 #1751
[instance] 0 #1752
[attach-enode] #1752 0
[end-of-instance]
[mk-quant] #1752 internal_alloc__sync__impl&__117_trait_impl_definition 4 #1749 #1751
[attach-var-names] #1752 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #1753 ens%the_q!model.lemma_pow2_pos. #123
[mk-app] #1754 the_q!model.pow2.? #166
[mk-app] #1755 > #1754 #337
[mk-app] #1756 = #1753 #1755
[mk-app] #1757 pattern #1753
[mk-quant] #1758 internal_ens__the_q!model.lemma_pow2_pos._definition 1 #1757 #1756
[attach-var-names] #1758 (|n!| ; |Int|)
[mk-app] #1759 <= #1754 #337
[mk-app] #1760 not #1759
[inst-discovered] theory-solving 0 arith# ; #1755
[mk-app] #1761 = #1755 #1760
[instance] 0 #1761
[attach-enode] #1761 0
[end-of-instance]
[mk-app] #1761 = #1759 #1753
[mk-app] #1762 not #1761
[mk-app] #1763 = #1753 #1760
[inst-discovered] theory-solving 0 basic# ; #1763
[mk-app] #1764 = #1763 #1762
[instance] 0 #1764
[attach-enode] #1764 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #1763 = #1762 #1762
[instance] 0 #1763
[attach-enode] #1763 0
[end-of-instance]
[mk-quant] #1763 internal_ens__the_q!model.lemma_pow2_pos._definition 1 #1757 #1762
[attach-var-names] #1763 (|n!| ; |Int|)
[mk-app] #1760 req%the_q!model.lemma_pow2_mono. #220 #123
[mk-app] #1764 %%global_location_label%%0
[mk-app] #1765 <= #220 #123
[mk-app] #1766 => #1764 #1765
[mk-app] #1767 = #1760 #1766
[mk-app] #1768 pattern #1760
[mk-quant] #1769 internal_req__the_q!model.lemma_pow2_mono._definition 2 #1768 #1767
[attach-var-names] #1769 (|b!| ; |Int|) (|a!| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #1770 * #366 #123
[mk-app] #1771 + #1770 #220
[attach-meaning] #366 arith (- 1)
[mk-app] #1770 >= #778 #337
[inst-discovered] theory-solving 0 arith# ; #1765
[mk-app] #1771 = #1765 #1770
[instance] 0 #1771
[attach-enode] #1771 0
[end-of-instance]
[mk-app] #1771 not #1764
[mk-app] #1772 or #1771 #1770
[mk-app] #1773 => #1764 #1770
[inst-discovered] theory-solving 0 basic# ; #1773
[mk-app] #1774 = #1773 #1772
[instance] 0 #1774
[attach-enode] #1774 0
[end-of-instance]
[mk-app] #1773 = #1760 #1772
[mk-quant] #1774 internal_req__the_q!model.lemma_pow2_mono._definition 2 #1768 #1773
[attach-var-names] #1774 (|b!| ; |Int|) (|a!| ; |Int|)
[mk-app] #1775 ens%the_q!model.lemma_pow2_mono. #220 #123
[mk-app] #1776 the_q!model.pow2.? #767
[mk-app] #1777 <= #1776 #1754
[mk-app] #1778 = #1775 #1777
[mk-app] #1779 pattern #1775
[mk-quant] #1780 internal_ens__the_q!model.lemma_pow2_mono._definition 2 #1779 #1778
[attach-var-names] #1780 (|b!| ; |Int|) (|a!| ; |Int|)
[attach-meaning] #366 arith (- 1)
[mk-app] #1781 * #366 #1754
[mk-app] #1782 + #1781 #1776
[attach-meaning] #366 arith (- 1)
[mk-app] #1783 * #366 #1776
[mk-app] #1784 + #1754 #1783
[mk-app] #1781 >= #1784 #337
[inst-discovered] theory-solving 0 arith# ; #1777
[mk-app] #1782 = #1777 #1781
[instance] 0 #1782
[attach-enode] #1782 0
[end-of-instance]
[mk-app] #1782 = #1775 #1781
[mk-quant] #1785 internal_ens__the_q!model.lemma_pow2_mono._definition 2 #1779 #1782
[attach-var-names] #1785 (|b!| ; |Int|) (|a!| ; |Int|)
[mk-app] #1786 ens%the_q!model.lemma_pow2_add. #220 #123
[mk-app] #1787 nClip #543
[mk-app] #1788 I #1787
[mk-app] #1789 the_q!model.pow2.? #1788
[mk-app] #1790 Mul #1776 #1754
[mk-app] #1791 = #1789 #1790
[mk-app] #1792 = #1786 #1791
[mk-app] #1793 pattern #1786
[mk-quant] #1794 internal_ens__the_q!model.lemma_pow2_add._definition 2 #1793 #1792
[attach-var-names] #1794 (|b!| ; |Int|) (|a!| ; |Int|)
[inst-discovered] theory-solving 0 basic# ; #914
[mk-app] #1795 = #914 #914
[instance] 0 #1795
[attach-enode] #1795 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #919
[mk-app] #1795 = #919 #919
[instance] 0 #1795
[attach-enode] #1795 0
[end-of-instance]
[mk-app] #1795 not #1
[inst-discovered] theory-solving 0 basic# ; #1795
[mk-app] #1796 = #1795 #2
[instance] 0 #1796
[attach-enode] #1796 0
[end-of-instance]
[mk-app] #1795 or #2 #943
[inst-discovered] theory-solving 0 basic# ; #1795
[mk-app] #1796 = #1795 #943
[instance] 0 #1796
[attach-enode] #1796 0
[end-of-instance]
[mk-app] #945 not #1527
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #945 = #1530 #1530
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[mk-app] #945 not #1759
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #945 = #1762 #1762
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[mk-app] #945 not #1759
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #945 = #1762 #1762
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[mk-app] #945 not #1527
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #945 = #1530 #1530
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #919
[mk-app] #945 = #919 #919
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #914
[mk-app] #945 = #914 #914
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #914
[mk-app] #945 = #914 #914
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #919
[mk-app] #945 = #919 #919
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[mk-app] #945 not #1527
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #945 = #1530 #1530
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[mk-app] #945 not #1759
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #945 = #1762 #1762
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #914
[mk-app] #945 = #914 #914
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #919
[mk-app] #945 = #919 #919
[instance] 0 #945
[attach-enode] #945 0
[end-of-instance]
[mk-app] #945 not #1256
[mk-app] #946 k$!skolem_user_the_q__model__divides_2!0 #34 #33
[mk-app] #1795 Mul #672 #946
[mk-app] #1796 = #187 #1795
[mk-app] #1797 not #1258
[mk-quant] #1798 user_the_q__model__divides_2 1 #1259 #1797
[attach-var-names] #1798 (|k$| ; |Int|)
[mk-app] #1799 or #1256 #1798
[mk-app] #1800 or #945 #1796
[mk-app] #1801 and #1800 #1799
[mk-quant] #1802 internal_the_q!model.divides.?_definition 2 #1262 #1801
[attach-var-names] #1802 (|n!| ; |Poly|) (|d!| ; |Poly|)
[mk-app] #1803 or #1265 #1802
[mk-app] #1804 not #1527
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #1804 = #1530 #1530
[instance] 0 #1804
[attach-enode] #1804 0
[end-of-instance]
[mk-app] #1804 not #1759
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #1804 = #1762 #1762
[instance] 0 #1804
[attach-enode] #1804 0
[end-of-instance]
[mk-app] #1266 not #68
[mk-app] #1804 not #69
[mk-app] #1805 or #1266 #1804
[mk-app] #1806 not #1805
[inst-discovered] theory-solving 0 basic# ; #70
[mk-app] #1807 = #70 #1806
[instance] 0 #1807
[attach-enode] #1807 0
[end-of-instance]
[mk-app] #1807 not #1806
[inst-discovered] theory-solving 0 basic# ; #1807
[mk-app] #1808 = #1807 #1805
[instance] 0 #1808
[attach-enode] #1808 0
[end-of-instance]
[mk-app] #1807 or #1266 #1804 #72
[mk-app] #1808 or #1805 #72
[inst-discovered] theory-solving 0 basic# ; #1808
[mk-app] #1809 = #1808 #1807
[instance] 0 #1809
[attach-enode] #1809 0
[end-of-instance]
[mk-quant] #1808 prelude_mut_ref_update_has_type 4 #74 #1807
[attach-var-names] #1808 (|arg| ; |Poly|) (|t| ; |Type|) (|d| ; |Dcr|) (|m| ; |Poly|)
[mk-app] #1805 not #146
[mk-app] #1806 not #154
[mk-app] #1809 or #1805 #1806
[mk-app] #1810 not #1809
[inst-discovered] theory-solving 0 basic# ; #155
[mk-app] #1811 = #155 #1810
[instance] 0 #1811
[attach-enode] #1811 0
[end-of-instance]
[mk-quant] #1811 prelude_as_type 2 #151 #1810
[attach-var-names] #1811 (|t| ; |Type|) (|x| ; |Poly|)
[mk-app] #1812 not #348
[mk-app] #1813 not #347
[mk-app] #1814 or #1812 #1813
[mk-app] #1815 not #1814
[inst-discovered] theory-solving 0 basic# ; #350
[mk-app] #1816 = #350 #1815
[instance] 0 #1816
[attach-enode] #1816 0
[end-of-instance]
[mk-quant] #1816 prelude_nat_clip 1 #344 #1815
[attach-var-names] #1816 (|i| ; |Int|)
[mk-app] #1817 or #346 #373
[mk-app] #1818 not #1817
[inst-discovered] theory-solving 0 basic# ; #376
[mk-app] #1819 = #376 #1818
[instance] 0 #1819
[attach-enode] #1819 0
[end-of-instance]
[mk-app] #1819 not #1818
[inst-discovered] theory-solving 0 basic# ; #1819
[mk-app] #1820 = #1819 #1817
[instance] 0 #1820
[attach-enode] #1820 0
[end-of-instance]
[mk-app] #1819 or #346 #373 #358
[mk-app] #1820 or #1817 #358
[inst-discovered] theory-solving 0 basic# ; #1820
[mk-app] #1821 = #1820 #1819
[instance] 0 #1821
[attach-enode] #1821 0
[end-of-instance]
[mk-app] #1820 not #365
[mk-app] #1821 not #1819
[mk-app] #1822 or #1820 #367 #1821
[mk-app] #1823 not #1822
[mk-app] #1824 and #365 #368 #1819
[inst-discovered] theory-solving 0 basic# ; #1824
[mk-app] #1825 = #1824 #1823
[instance] 0 #1825
[attach-enode] #1825 0
[end-of-instance]
[mk-quant] #1824 prelude_u_clip 2 #361 #1823
[attach-var-names] #1824 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #1817 not #399
[mk-app] #1818 or #1817 #404
[mk-app] #1825 not #1818
[inst-discovered] theory-solving 0 basic# ; #407
[mk-app] #1826 = #407 #1825
[instance] 0 #1826
[attach-enode] #1826 0
[end-of-instance]
[mk-app] #1826 not #1825
[inst-discovered] theory-solving 0 basic# ; #1826
[mk-app] #1827 = #1826 #1818
[instance] 0 #1827
[attach-enode] #1827 0
[end-of-instance]
[mk-app] #1826 or #1817 #404 #385
[mk-app] #1827 or #1818 #385
[inst-discovered] theory-solving 0 basic# ; #1827
[mk-app] #1828 = #1827 #1826
[instance] 0 #1828
[attach-enode] #1828 0
[end-of-instance]
[mk-app] #1827 not #392
[mk-app] #1828 not #1826
[mk-app] #1829 or #1827 #395 #1828
[mk-app] #1830 not #1829
[mk-app] #1831 and #392 #398 #1826
[inst-discovered] theory-solving 0 basic# ; #1831
[mk-app] #1832 = #1831 #1830
[instance] 0 #1832
[attach-enode] #1832 0
[end-of-instance]
[mk-quant] #1831 prelude_i_clip 2 #388 #1830
[attach-var-names] #1831 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #1818 not #431
[mk-app] #1825 not #394
[mk-app] #1832 or #1818 #1825
[mk-app] #1833 not #1832
[inst-discovered] theory-solving 0 basic# ; #430
[mk-app] #1834 = #430 #1833
[instance] 0 #1834
[attach-enode] #1834 0
[end-of-instance]
[mk-app] #1834 not #434
[mk-app] #1835 not #416
[mk-app] #1836 or #1834 #1835
[mk-app] #1837 not #1836
[inst-discovered] theory-solving 0 basic# ; #432
[mk-app] #1838 = #432 #1837
[instance] 0 #1838
[attach-enode] #1838 0
[end-of-instance]
[mk-app] #1838 or #1833 #1837
[mk-app] #1839 not #419
[mk-app] #1840 or #346 #1839
[mk-app] #1841 not #1840
[inst-discovered] theory-solving 0 basic# ; #435
[mk-app] #1842 = #435 #1841
[instance] 0 #1842
[attach-enode] #1842 0
[end-of-instance]
[mk-app] #1842 not #438
[mk-app] #1843 not #422
[mk-app] #1844 or #1842 #1843
[mk-app] #1845 not #1844
[inst-discovered] theory-solving 0 basic# ; #436
[mk-app] #1846 = #436 #1845
[instance] 0 #1846
[attach-enode] #1846 0
[end-of-instance]
[mk-app] #1846 or #1841 #1845
[mk-app] #1847 not #1846
[mk-app] #1848 or #1847 #425
[mk-app] #1849 not #1838
[mk-app] #1850 not #1848
[mk-app] #1851 or #1849 #1850
[mk-app] #1852 not #1851
[mk-app] #1853 and #1838 #1848
[inst-discovered] theory-solving 0 basic# ; #1853
[mk-app] #1854 = #1853 #1852
[instance] 0 #1854
[attach-enode] #1854 0
[end-of-instance]
[mk-quant] #1853 prelude_char_clip 1 #428 #1852
[attach-var-names] #1853 (|i| ; |Int|)
[mk-app] #1854 or #346 #373
[mk-app] #1855 not #1854
[inst-discovered] theory-solving 0 basic# ; #376
[mk-app] #1856 = #376 #1855
[instance] 0 #1856
[attach-enode] #1856 0
[end-of-instance]
[mk-app] #1856 = #1854 #443
[mk-app] #1857 not #1856
[mk-app] #1858 = #443 #1855
[inst-discovered] theory-solving 0 basic# ; #1858
[mk-app] #1859 = #1858 #1857
[instance] 0 #1859
[attach-enode] #1859 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1857
[mk-app] #1858 = #1857 #1857
[instance] 0 #1858
[attach-enode] #1858 0
[end-of-instance]
[mk-quant] #1858 prelude_u_inv 2 #445 #1857
[attach-var-names] #1858 (|i| ; |Int|) (|bits| ; |Int|)
[mk-app] #1855 or #1817 #404
[mk-app] #1859 not #1855
[inst-discovered] theory-solving 0 basic# ; #407
[mk-app] #1860 = #407 #1859
[instance] 0 #1860
[attach-enode] #1860 0
[end-of-instance]
[mk-app] #1860 = #1855 #447
[mk-app] #1861 not #1860
[mk-app] #1862 = #447 #1859
[inst-discovered] theory-solving 0 basic# ; #1862
[mk-app] #1863 = #1862 #1861
[instance] 0 #1863
[attach-enode] #1863 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1861
[mk-app] #1862 = #1861 #1861
[instance] 0 #1862
[attach-enode] #1862 0
[end-of-instance]
[mk-quant] #1862 prelude_i_inv 2 #451 #1861
[attach-var-names] #1862 (|i| ; |Int|) (|bits| ; |Int|)
[inst-discovered] theory-solving 0 basic# ; #435
[mk-app] #1859 = #435 #1841
[instance] 0 #1859
[attach-enode] #1859 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #436
[mk-app] #1859 = #436 #1845
[instance] 0 #1859
[attach-enode] #1859 0
[end-of-instance]
[mk-app] #1859 = #453 #1846
[mk-quant] #1863 prelude_char_inv 1 #457 #1859
[attach-var-names] #1863 (|i| ; |Int|)
[mk-app] #1864 not #633
[mk-app] #1865 or #1864 #346
[mk-app] #1866 not #1865
[inst-discovered] theory-solving 0 basic# ; #634
[mk-app] #1867 = #634 #1866
[instance] 0 #1867
[attach-enode] #1867 0
[end-of-instance]
[mk-app] #1867 not #1866
[inst-discovered] theory-solving 0 basic# ; #1867
[mk-app] #1868 = #1867 #1865
[instance] 0 #1868
[attach-enode] #1868 0
[end-of-instance]
[mk-app] #1866 or #1864 #346 #636
[mk-app] #1867 or #1865 #636
[inst-discovered] theory-solving 0 basic# ; #1867
[mk-app] #1868 = #1867 #1866
[instance] 0 #1868
[attach-enode] #1868 0
[end-of-instance]
[mk-quant] #1865 prelude_mul_nats 2 #564 #1866
[attach-var-names] #1865 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #1867 or #1864 #646
[mk-app] #1868 not #1867
[inst-discovered] theory-solving 0 basic# ; #648
[mk-app] #1869 = #648 #1868
[instance] 0 #1869
[attach-enode] #1869 0
[end-of-instance]
[mk-app] #1869 not #1868
[inst-discovered] theory-solving 0 basic# ; #1869
[mk-app] #1870 = #1869 #1867
[instance] 0 #1870
[attach-enode] #1870 0
[end-of-instance]
[mk-app] #1868 not #650
[mk-app] #1869 not #649
[mk-app] #1870 or #1868 #1869
[mk-app] #1871 not #1870
[inst-discovered] theory-solving 0 basic# ; #653
[mk-app] #1872 = #653 #1871
[instance] 0 #1872
[attach-enode] #1872 0
[end-of-instance]
[mk-app] #1872 or #1864 #646 #1871
[mk-app] #1873 or #1867 #1871
[inst-discovered] theory-solving 0 basic# ; #1873
[mk-app] #1874 = #1873 #1872
[instance] 0 #1874
[attach-enode] #1874 0
[end-of-instance]
[mk-quant] #1873 prelude_div_unsigned_in_bounds 2 #574 #1872
[attach-var-names] #1873 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #1867 or #1864 #646
[mk-app] #1874 not #1867
[inst-discovered] theory-solving 0 basic# ; #648
[mk-app] #1875 = #648 #1874
[instance] 0 #1875
[attach-enode] #1875 0
[end-of-instance]
[mk-app] #1875 not #1874
[inst-discovered] theory-solving 0 basic# ; #1875
[mk-app] #1876 = #1875 #1867
[instance] 0 #1876
[attach-enode] #1876 0
[end-of-instance]
[mk-app] #1874 not #663
[mk-app] #1875 or #1874 #667
[mk-app] #1876 not #1875
[inst-discovered] theory-solving 0 basic# ; #669
[mk-app] #1877 = #669 #1876
[instance] 0 #1877
[attach-enode] #1877 0
[end-of-instance]
[mk-app] #1877 or #1864 #646 #1876
[mk-app] #1878 or #1867 #1876
[inst-discovered] theory-solving 0 basic# ; #1878
[mk-app] #1879 = #1878 #1877
[instance] 0 #1879
[attach-enode] #1879 0
[end-of-instance]
[mk-quant] #1878 prelude_mod_unsigned_in_bounds 2 #583 #1877
[attach-var-names] #1878 (|y| ; |Int|) (|x| ; |Int|)
[mk-app] #1867 not #664
[mk-app] #1879 not #673
[mk-app] #1880 or #1867 #1879
[mk-app] #1881 not #1880
[inst-discovered] theory-solving 0 basic# ; #674
[mk-app] #1882 = #674 #1881
[instance] 0 #1882
[attach-enode] #1882 0
[end-of-instance]
[mk-app] #1882 not #1881
[inst-discovered] theory-solving 0 basic# ; #1882
[mk-app] #1883 = #1882 #1880
[instance] 0 #1883
[attach-enode] #1883 0
[end-of-instance]
[mk-app] #1882 or #1867 #1879 #676
[mk-app] #1883 or #1880 #676
[inst-discovered] theory-solving 0 basic# ; #1883
[mk-app] #1884 = #1883 #1882
[instance] 0 #1884
[attach-enode] #1884 0
[end-of-instance]
[mk-quant] #1883 prelude_bit_xor_u_inv 3 #679 #1882
[attach-var-names] #1883 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1880 not #684
[mk-app] #1881 not #685
[mk-app] #1884 or #1880 #1881
[mk-app] #1885 not #1884
[inst-discovered] theory-solving 0 basic# ; #686
[mk-app] #1886 = #686 #1885
[instance] 0 #1886
[attach-enode] #1886 0
[end-of-instance]
[mk-app] #1886 not #1885
[inst-discovered] theory-solving 0 basic# ; #1886
[mk-app] #1887 = #1886 #1884
[instance] 0 #1887
[attach-enode] #1887 0
[end-of-instance]
[mk-app] #1886 or #1880 #1881 #687
[mk-app] #1887 or #1884 #687
[inst-discovered] theory-solving 0 basic# ; #1887
[mk-app] #1888 = #1887 #1886
[instance] 0 #1888
[attach-enode] #1888 0
[end-of-instance]
[mk-quant] #1887 prelude_bit_xor_i_inv 3 #690 #1886
[attach-var-names] #1887 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1884 or #1867 #1879
[mk-app] #1885 not #1884
[inst-discovered] theory-solving 0 basic# ; #674
[mk-app] #1888 = #674 #1885
[instance] 0 #1888
[attach-enode] #1888 0
[end-of-instance]
[mk-app] #1888 not #1885
[inst-discovered] theory-solving 0 basic# ; #1888
[mk-app] #1889 = #1888 #1884
[instance] 0 #1889
[attach-enode] #1889 0
[end-of-instance]
[mk-app] #1888 or #1867 #1879 #696
[mk-app] #1889 or #1884 #696
[inst-discovered] theory-solving 0 basic# ; #1889
[mk-app] #1890 = #1889 #1888
[instance] 0 #1890
[attach-enode] #1890 0
[end-of-instance]
[mk-quant] #1889 prelude_bit_or_u_inv 3 #699 #1888
[attach-var-names] #1889 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1884 or #1880 #1881
[mk-app] #1885 not #1884
[inst-discovered] theory-solving 0 basic# ; #686
[mk-app] #1890 = #686 #1885
[instance] 0 #1890
[attach-enode] #1890 0
[end-of-instance]
[mk-app] #1890 not #1885
[inst-discovered] theory-solving 0 basic# ; #1890
[mk-app] #1891 = #1890 #1884
[instance] 0 #1891
[attach-enode] #1891 0
[end-of-instance]
[mk-app] #1890 or #1880 #1881 #703
[mk-app] #1891 or #1884 #703
[inst-discovered] theory-solving 0 basic# ; #1891
[mk-app] #1892 = #1891 #1890
[instance] 0 #1892
[attach-enode] #1892 0
[end-of-instance]
[mk-quant] #1891 prelude_bit_or_i_inv 3 #706 #1890
[attach-var-names] #1891 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1884 or #1867 #1879
[mk-app] #1885 not #1884
[inst-discovered] theory-solving 0 basic# ; #674
[mk-app] #1892 = #674 #1885
[instance] 0 #1892
[attach-enode] #1892 0
[end-of-instance]
[mk-app] #1892 not #1885
[inst-discovered] theory-solving 0 basic# ; #1892
[mk-app] #1893 = #1892 #1884
[instance] 0 #1893
[attach-enode] #1893 0
[end-of-instance]
[mk-app] #1892 or #1867 #1879 #711
[mk-app] #1893 or #1884 #711
[inst-discovered] theory-solving 0 basic# ; #1893
[mk-app] #1894 = #1893 #1892
[instance] 0 #1894
[attach-enode] #1894 0
[end-of-instance]
[mk-quant] #1893 prelude_bit_and_u_inv 3 #714 #1892
[attach-var-names] #1893 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1884 or #1880 #1881
[mk-app] #1885 not #1884
[inst-discovered] theory-solving 0 basic# ; #686
[mk-app] #1894 = #686 #1885
[instance] 0 #1894
[attach-enode] #1894 0
[end-of-instance]
[mk-app] #1894 not #1885
[inst-discovered] theory-solving 0 basic# ; #1894
[mk-app] #1895 = #1894 #1884
[instance] 0 #1895
[attach-enode] #1895 0
[end-of-instance]
[mk-app] #1894 or #1880 #1881 #718
[mk-app] #1895 or #1884 #718
[inst-discovered] theory-solving 0 basic# ; #1895
[mk-app] #1896 = #1895 #1894
[instance] 0 #1896
[attach-enode] #1896 0
[end-of-instance]
[mk-quant] #1895 prelude_bit_and_i_inv 3 #721 #1894
[attach-var-names] #1895 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1884 not #734
[mk-app] #1885 or #1867 #1884
[mk-app] #1896 not #1885
[inst-discovered] theory-solving 0 basic# ; #733
[mk-app] #1897 = #733 #1896
[instance] 0 #1897
[attach-enode] #1897 0
[end-of-instance]
[mk-app] #1897 not #1896
[inst-discovered] theory-solving 0 basic# ; #1897
[mk-app] #1898 = #1897 #1885
[instance] 0 #1898
[attach-enode] #1898 0
[end-of-instance]
[mk-app] #1896 or #1867 #1884 #728
[mk-app] #1897 or #1885 #728
[inst-discovered] theory-solving 0 basic# ; #1897
[mk-app] #1898 = #1897 #1896
[instance] 0 #1898
[attach-enode] #1898 0
[end-of-instance]
[mk-quant] #1885 prelude_bit_shr_u_inv 3 #731 #1896
[attach-var-names] #1885 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1897 or #1880 #1884
[mk-app] #1898 not #1897
[inst-discovered] theory-solving 0 basic# ; #744
[mk-app] #1899 = #744 #1898
[instance] 0 #1899
[attach-enode] #1899 0
[end-of-instance]
[mk-app] #1899 not #1898
[inst-discovered] theory-solving 0 basic# ; #1899
[mk-app] #1900 = #1899 #1897
[instance] 0 #1900
[attach-enode] #1900 0
[end-of-instance]
[mk-app] #1898 or #1880 #1884 #739
[mk-app] #1899 or #1897 #739
[inst-discovered] theory-solving 0 basic# ; #1899
[mk-app] #1900 = #1899 #1898
[instance] 0 #1900
[attach-enode] #1900 0
[end-of-instance]
[mk-quant] #1897 prelude_bit_shr_i_inv 3 #742 #1898
[attach-var-names] #1897 (|bits| ; |Int|) (|y| ; |Poly|) (|x| ; |Poly|)
[mk-app] #1899 not #761
[mk-app] #1900 not #129
[mk-app] #1901 or #1899 #1900
[mk-app] #1902 not #1901
[inst-discovered] theory-solving 0 basic# ; #762
[mk-app] #1903 = #762 #1902
[instance] 0 #1903
[attach-enode] #1903 0
[end-of-instance]
[mk-app] #1903 or #760 #1902
[inst-discovered] theory-solving 0 basic# ; #1903
[mk-app] #1904 = #1903 #1903
[instance] 0 #1904
[attach-enode] #1904 0
[end-of-instance]
[mk-app] #1904 = #757 #1903
[mk-quant] #1905 prelude_check_decrease_height 3 #765 #1904
[attach-var-names] #1905 (|otherwise| ; |Bool|) (|prev| ; |Poly|) (|cur| ; |Poly|)
[mk-app] #1906 or #1864 #779
[mk-app] #1907 not #1906
[inst-discovered] theory-solving 0 basic# ; #781
[mk-app] #1908 = #781 #1907
[instance] 0 #1908
[attach-enode] #1908 0
[end-of-instance]
[mk-app] #1908 = #1906 #770
[mk-app] #1909 not #1908
[mk-app] #1910 = #770 #1907
[inst-discovered] theory-solving 0 basic# ; #1910
[mk-app] #1911 = #1910 #1909
[instance] 0 #1911
[attach-enode] #1911 0
[end-of-instance]
[mk-app] #1907 not #1906
[inst-discovered] theory-solving 0 basic# ; #1909
[mk-app] #1907 = #1909 #1909
[instance] 0 #1907
[attach-enode] #1907 0
[end-of-instance]
[mk-quant] #1907 prelude_check_decrease_int_height 2 #774 #1909
[attach-var-names] #1907 (|prev| ; |Int|) (|cur| ; |Int|)
[mk-app] #1910 not #785
[mk-app] #1911 or #1910 #786
[mk-app] #1912 not #1911
[inst-discovered] theory-solving 0 basic# ; #788
[mk-app] #1913 = #788 #1912
[instance] 0 #1913
[attach-enode] #1913 0
[end-of-instance]
[mk-app] #1913 = #1911 #784
[mk-app] #1914 not #1913
[mk-app] #1915 = #784 #1912
[inst-discovered] theory-solving 0 basic# ; #1915
[mk-app] #1916 = #1915 #1914
[instance] 0 #1916
[attach-enode] #1916 0
[end-of-instance]
[mk-app] #1912 not #1911
[inst-discovered] theory-solving 0 basic# ; #1914
[mk-app] #1912 = #1914 #1914
[instance] 0 #1912
[attach-enode] #1912 0
[end-of-instance]
[mk-quant] #1912 prelude_height_lt 2 #790 #1914
[attach-var-names] #1912 (|y| ; |Height|) (|x| ; |Height|)
[mk-app] #1915 not #874
[mk-app] #1916 not #875
[mk-app] #1917 or #1915 #1916
[mk-app] #1918 not #1917
[inst-discovered] theory-solving 0 basic# ; #876
[mk-app] #1919 = #876 #1918
[instance] 0 #1919
[attach-enode] #1919 0
[end-of-instance]
[mk-app] #1919 or #878 #1918
[mk-app] #1920 not #881
[mk-app] #1921 not #882
[mk-app] #1922 not #883
[mk-app] #1923 not #884
[mk-app] #1924 not #885
[mk-app] #1925 not #886
[mk-app] #1926 not #887
[mk-app] #1927 not #888
[mk-app] #1928 not #889
[mk-app] #1929 not #890
[mk-app] #1930 not #891
[mk-app] #1931 not #892
[mk-app] #1932 not #893
[mk-app] #1933 not #894
[mk-app] #1934 not #895
[mk-app] #1935 not #896
[mk-app] #1936 not #897
[mk-app] #1937 not #898
[mk-app] #1938 not #899
[mk-app] #1939 not #900
[mk-app] #1940 not #901
[mk-app] #1941 not #902
[mk-app] #1942 not #903
[mk-app] #1943 not #904
[mk-app] #1944 not #905
[mk-app] #1945 or #1920 #1921 #1922 #1923 #1924 #1925 #1926 #1927 #1928 #1929 #1930 #1931 #1932 #1933 #1934 #1935 #1936 #1937 #1938 #1939 #1940 #1941 #1942 #1943 #1944
[mk-app] #1946 not #1945
[inst-discovered] theory-solving 0 basic# ; #906
[mk-app] #1947 = #906 #1946
[instance] 0 #1947
[attach-enode] #1947 0
[end-of-instance]
[mk-app] #1947 or #908 #1946
[inst-discovered] theory-solving 0 basic# ; #914
[mk-app] #1948 = #914 #914
[instance] 0 #1948
[attach-enode] #1948 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #919
[mk-app] #1948 = #919 #919
[instance] 0 #1948
[attach-enode] #1948 0
[end-of-instance]
[mk-app] #1948 not #964
[mk-app] #1949 not #965
[mk-app] #1950 or #1948 #1949
[mk-app] #1951 not #1950
[inst-discovered] theory-solving 0 basic# ; #966
[mk-app] #1952 = #966 #1951
[instance] 0 #1952
[attach-enode] #1952 0
[end-of-instance]
[mk-app] #1952 not #1951
[inst-discovered] theory-solving 0 basic# ; #1952
[mk-app] #1953 = #1952 #1950
[instance] 0 #1953
[attach-enode] #1953 0
[end-of-instance]
[mk-app] #1952 or #1948 #1949 #969
[mk-app] #1953 or #1950 #969
[inst-discovered] theory-solving 0 basic# ; #1953
[mk-app] #1954 = #1953 #1952
[instance] 0 #1954
[attach-enode] #1954 0
[end-of-instance]
[mk-quant] #1953 internal_the_q!types.Q./Q_constructor_definition 2 #971 #1952
[attach-var-names] #1953 (|_den!| ; |Int|) (|_num!| ; |Int|)
[mk-app] #1950 not #1025
[mk-app] #1951 not #1020
[mk-app] #1954 not #1027
[mk-app] #1955 or #1950 #1951 #1954
[mk-app] #1956 not #1955
[inst-discovered] theory-solving 0 basic# ; #1028
[mk-app] #1957 = #1028 #1956
[instance] 0 #1957
[attach-enode] #1957 0
[end-of-instance]
[mk-app] #1957 or #1032 #1956
[mk-quant] #1958 internal_core__ops__function__FnOnce_trait_type_bounds_definition 4 #1030 #1957
[attach-var-names] #1958 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1959 or #1032 #1950 #1951
[mk-app] #1960 not #1959
[inst-discovered] theory-solving 0 basic# ; #1036
[mk-app] #1961 = #1036 #1960
[instance] 0 #1961
[attach-enode] #1961 0
[end-of-instance]
[mk-app] #1961 or #1040 #1960
[mk-quant] #1962 internal_core__ops__function__FnMut_trait_type_bounds_definition 4 #1038 #1961
[attach-var-names] #1962 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1963 or #1040 #1950 #1951
[mk-app] #1964 not #1963
[inst-discovered] theory-solving 0 basic# ; #1044
[mk-app] #1965 = #1044 #1964
[instance] 0 #1965
[attach-enode] #1965 0
[end-of-instance]
[mk-app] #1965 or #1048 #1964
[mk-quant] #1966 internal_core__ops__function__Fn_trait_type_bounds_definition 4 #1046 #1965
[attach-var-names] #1966 (|Args&| ; |Type|) (|Args&.| ; |Dcr|) (|Self%&| ; |Type|) (|Self%&.| ; |Dcr|)
[mk-app] #1967 not #1054
[mk-app] #1968 not #1055
[mk-app] #1969 not #1056
[mk-app] #1970 or #1967 #1968 #1969
[mk-app] #1971 not #1970
[inst-discovered] theory-solving 0 basic# ; #1057
[mk-app] #1972 = #1057 #1971
[instance] 0 #1972
[attach-enode] #1972 0
[end-of-instance]
[mk-app] #1972 not #1971
[inst-discovered] theory-solving 0 basic# ; #1972
[mk-app] #1973 = #1972 #1970
[instance] 0 #1973
[attach-enode] #1973 0
[end-of-instance]
[mk-app] #1972 or #1967 #1968 #1969 #1061
[mk-app] #1973 or #1970 #1061
[inst-discovered] theory-solving 0 basic# ; #1973
[mk-app] #1974 = #1973 #1972
[instance] 0 #1974
[attach-enode] #1974 0
[end-of-instance]
[mk-quant] #1973 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 4 #1063 #1972
[attach-var-names] #1973 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1970 or #1967 #1968 #1969
[mk-app] #1971 not #1970
[inst-discovered] theory-solving 0 basic# ; #1057
[mk-app] #1974 = #1057 #1971
[instance] 0 #1974
[attach-enode] #1974 0
[end-of-instance]
[mk-app] #1974 not #1971
[inst-discovered] theory-solving 0 basic# ; #1974
[mk-app] #1975 = #1974 #1970
[instance] 0 #1975
[attach-enode] #1975 0
[end-of-instance]
[mk-app] #1974 or #1967 #1968 #1969 #1070
[mk-app] #1975 or #1970 #1070
[inst-discovered] theory-solving 0 basic# ; #1975
[mk-app] #1976 = #1975 #1974
[instance] 0 #1976
[attach-enode] #1976 0
[end-of-instance]
[mk-quant] #1975 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 4 #1072 #1974
[attach-var-names] #1975 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1970 not #1076
[mk-app] #1971 or #1967 #1968 #1970
[mk-app] #1976 not #1971
[inst-discovered] theory-solving 0 basic# ; #1077
[mk-app] #1977 = #1077 #1976
[instance] 0 #1977
[attach-enode] #1977 0
[end-of-instance]
[mk-app] #1977 not #1976
[inst-discovered] theory-solving 0 basic# ; #1977
[mk-app] #1978 = #1977 #1971
[instance] 0 #1978
[attach-enode] #1978 0
[end-of-instance]
[mk-app] #1977 or #1967 #1968 #1970 #1079
[mk-app] #1978 or #1971 #1079
[inst-discovered] theory-solving 0 basic# ; #1978
[mk-app] #1979 = #1978 #1977
[instance] 0 #1979
[attach-enode] #1979 0
[end-of-instance]
[mk-quant] #1978 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 4 #1081 #1977
[attach-var-names] #1978 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1971 or #1967 #1968 #1970
[mk-app] #1976 not #1971
[inst-discovered] theory-solving 0 basic# ; #1077
[mk-app] #1979 = #1077 #1976
[instance] 0 #1979
[attach-enode] #1979 0
[end-of-instance]
[mk-app] #1979 not #1976
[inst-discovered] theory-solving 0 basic# ; #1979
[mk-app] #1980 = #1979 #1971
[instance] 0 #1980
[attach-enode] #1980 0
[end-of-instance]
[mk-app] #1979 or #1967 #1968 #1970 #1087
[mk-app] #1980 or #1971 #1087
[inst-discovered] theory-solving 0 basic# ; #1980
[mk-app] #1981 = #1980 #1979
[instance] 0 #1981
[attach-enode] #1981 0
[end-of-instance]
[mk-quant] #1980 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 4 #1089 #1979
[attach-var-names] #1980 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1971 not #1095
[mk-app] #1976 not #1096
[mk-app] #1981 not #1097
[mk-app] #1982 or #1971 #1950 #1976 #1981 #1721
[mk-app] #1983 not #1982
[inst-discovered] theory-solving 0 basic# ; #1098
[mk-app] #1984 = #1098 #1983
[instance] 0 #1984
[attach-enode] #1984 0
[end-of-instance]
[mk-app] #1984 not #1983
[inst-discovered] theory-solving 0 basic# ; #1984
[mk-app] #1985 = #1984 #1982
[instance] 0 #1985
[attach-enode] #1985 0
[end-of-instance]
[mk-app] #1984 or #1971 #1950 #1976 #1981 #1721 #1102
[mk-app] #1985 or #1982 #1102
[inst-discovered] theory-solving 0 basic# ; #1985
[mk-app] #1986 = #1985 #1984
[instance] 0 #1986
[attach-enode] #1986 0
[end-of-instance]
[mk-quant] #1985 internal_proj____core!ops.function.FnOnce./Output_assoc_type_impl_true_definition 6 #1104 #1984
[attach-var-names] #1985 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1982 or #1971 #1950 #1976 #1981 #1721
[mk-app] #1983 not #1982
[inst-discovered] theory-solving 0 basic# ; #1098
[mk-app] #1986 = #1098 #1983
[instance] 0 #1986
[attach-enode] #1986 0
[end-of-instance]
[mk-app] #1986 not #1983
[inst-discovered] theory-solving 0 basic# ; #1986
[mk-app] #1987 = #1986 #1982
[instance] 0 #1987
[attach-enode] #1987 0
[end-of-instance]
[mk-app] #1986 or #1971 #1950 #1976 #1981 #1721 #1111
[mk-app] #1987 or #1982 #1111
[inst-discovered] theory-solving 0 basic# ; #1987
[mk-app] #1988 = #1987 #1986
[instance] 0 #1988
[attach-enode] #1988 0
[end-of-instance]
[mk-quant] #1987 internal_proj__core!ops.function.FnOnce./Output_assoc_type_impl_false_definition 6 #1113 #1986
[attach-var-names] #1987 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1982 or #1967 #1968 #1970
[mk-app] #1983 not #1982
[inst-discovered] theory-solving 0 basic# ; #1077
[mk-app] #1988 = #1077 #1983
[instance] 0 #1988
[attach-enode] #1988 0
[end-of-instance]
[mk-app] #1988 not #1983
[inst-discovered] theory-solving 0 basic# ; #1988
[mk-app] #1989 = #1988 #1982
[instance] 0 #1989
[attach-enode] #1989 0
[end-of-instance]
[mk-app] #1988 or #1967 #1968 #1970 #1117
[mk-app] #1989 or #1982 #1117
[inst-discovered] theory-solving 0 basic# ; #1989
[mk-app] #1990 = #1989 #1988
[instance] 0 #1990
[attach-enode] #1990 0
[end-of-instance]
[mk-quant] #1989 internal_core__ops__function__impls__impl&__4_trait_impl_definition 4 #1119 #1988
[attach-var-names] #1989 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #1982 not #1125
[mk-app] #1983 not #1126
[mk-app] #1990 or #1982 #1983
[mk-app] #1991 not #1990
[inst-discovered] theory-solving 0 basic# ; #1127
[mk-app] #1992 = #1127 #1991
[instance] 0 #1992
[attach-enode] #1992 0
[end-of-instance]
[mk-app] #1992 not #1991
[inst-discovered] theory-solving 0 basic# ; #1992
[mk-app] #1993 = #1992 #1990
[instance] 0 #1993
[attach-enode] #1993 0
[end-of-instance]
[mk-app] #1992 not #1130
[mk-app] #1993 not #1133
[mk-app] #1994 or #1971 #1967 #1976 #1992 #1993
[mk-app] #1995 not #1994
[inst-discovered] theory-solving 0 basic# ; #1141
[mk-app] #1996 = #1141 #1995
[instance] 0 #1996
[attach-enode] #1996 0
[end-of-instance]
[mk-app] #1996 not #1995
[inst-discovered] theory-solving 0 basic# ; #1996
[mk-app] #1997 = #1996 #1994
[instance] 0 #1997
[attach-enode] #1997 0
[end-of-instance]
[mk-app] #1995 or #1982 #1983 #1971 #1967 #1976 #1992 #1993 #1135
[mk-app] #1996 or #1990 #1994 #1135
[inst-discovered] theory-solving 0 basic# ; #1996
[mk-app] #1997 = #1996 #1995
[instance] 0 #1997
[attach-enode] #1997 0
[end-of-instance]
[mk-quant] #1994 user_vstd__function__axiom_fn_mut_call_requires_0 6 #1138 #1995
[attach-var-names] #1994 (|args!| ; |Poly|) (|f!| ; |Poly|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1990 or #1146 #1994
[mk-app] #1991 not #1154
[mk-app] #1996 not #1155
[mk-app] #1997 not #1157
[mk-app] #1998 or #1991 #1996 #1997
[mk-app] #1999 not #1998
[inst-discovered] theory-solving 0 basic# ; #1158
[mk-app] #2000 = #1158 #1999
[instance] 0 #2000
[attach-enode] #2000 0
[end-of-instance]
[mk-app] #2000 not #1999
[inst-discovered] theory-solving 0 basic# ; #2000
[mk-app] #2001 = #2000 #1998
[instance] 0 #2001
[attach-enode] #2001 0
[end-of-instance]
[mk-app] #2000 not #1159
[mk-app] #2001 not #1160
[mk-app] #2002 not #1162
[mk-app] #2003 not #1164
[mk-app] #2004 not #1166
[mk-app] #2005 or #2000 #2001 #2002 #2003 #2004
[mk-app] #2006 not #2005
[inst-discovered] theory-solving 0 basic# ; #1176
[mk-app] #2007 = #1176 #2006
[instance] 0 #2007
[attach-enode] #2007 0
[end-of-instance]
[mk-app] #2007 not #2006
[inst-discovered] theory-solving 0 basic# ; #2007
[mk-app] #2008 = #2007 #2005
[instance] 0 #2008
[attach-enode] #2008 0
[end-of-instance]
[mk-app] #2006 not #1168
[mk-app] #2007 not #1169
[mk-app] #2008 or #2006 #2007
[mk-app] #2009 not #2008
[inst-discovered] theory-solving 0 basic# ; #1170
[mk-app] #2010 = #1170 #2009
[instance] 0 #2010
[attach-enode] #2010 0
[end-of-instance]
[mk-app] #2010 or #1991 #1996 #1997 #2000 #2001 #2002 #2003 #2004 #2009
[mk-app] #2011 or #1998 #2005 #2009
[inst-discovered] theory-solving 0 basic# ; #2011
[mk-app] #2012 = #2011 #2010
[instance] 0 #2012
[attach-enode] #2012 0
[end-of-instance]
[mk-quant] #2005 user_vstd__function__axiom_fn_mut_call_ensures_1 7 #1173 #2010
[attach-var-names] #2005 (|output!| ; |Poly|) (|args!| ; |Poly|) (|f!| ; |Poly|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #1998 or #1181 #2005
[mk-app] #1999 not #1800
[mk-app] #2011 not #1799
[mk-app] #2012 or #1999 #2011
[mk-app] #2013 not #2012
[inst-discovered] theory-solving 0 basic# ; #1801
[mk-app] #2014 = #1801 #2013
[instance] 0 #2014
[attach-enode] #2014 0
[end-of-instance]
[mk-quant] #2014 internal_the_q!model.divides.?_definition 2 #1262 #2013
[attach-var-names] #2014 (|n!| ; |Poly|) (|d!| ; |Poly|)
[mk-app] #2015 or #1265 #2014
[mk-app] #2016 not #1273
[mk-app] #2017 or #2016 #1207
[mk-app] #2018 not #2017
[inst-discovered] theory-solving 0 basic# ; #1274
[mk-app] #2019 = #1274 #2018
[instance] 0 #2019
[attach-enode] #2019 0
[end-of-instance]
[mk-app] #2019 not #2018
[inst-discovered] theory-solving 0 basic# ; #2019
[mk-app] #2020 = #2019 #2017
[instance] 0 #2020
[attach-enode] #2020 0
[end-of-instance]
[mk-app] #2019 or #2016 #1207 #1280
[mk-app] #2020 or #2017 #1280
[inst-discovered] theory-solving 0 basic# ; #2020
[mk-app] #2021 = #2020 #2019
[instance] 0 #2021
[attach-enode] #2021 0
[end-of-instance]
[mk-quant] #2020 internal_the_q!model.gcd_nat._fuel_to_body_definition 3 #1282 #2019
[attach-var-names] #2020 (|fuel%| ; |Fuel|) (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #2017 or #1207 #201
[mk-app] #2018 not #2017
[inst-discovered] theory-solving 0 basic# ; #1288
[mk-app] #2021 = #1288 #2018
[instance] 0 #2021
[attach-enode] #2021 0
[end-of-instance]
[mk-app] #2021 not #2018
[inst-discovered] theory-solving 0 basic# ; #2021
[mk-app] #2022 = #2021 #2017
[instance] 0 #2022
[attach-enode] #2022 0
[end-of-instance]
[mk-app] #2021 or #1207 #201 #1293
[mk-app] #2022 or #2017 #1293
[inst-discovered] theory-solving 0 basic# ; #2022
[mk-app] #2023 = #2022 #2021
[instance] 0 #2023
[attach-enode] #2023 0
[end-of-instance]
[mk-quant] #2022 internal_the_q!model.gcd_nat.?_definition 2 #1295 #2021
[attach-var-names] #2022 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #2017 or #1301 #2022
[mk-app] #2018 or #1207 #201
[mk-app] #2023 not #2018
[inst-discovered] theory-solving 0 basic# ; #1288
[mk-app] #2024 = #1288 #2023
[instance] 0 #2024
[attach-enode] #2024 0
[end-of-instance]
[mk-app] #2024 not #2023
[inst-discovered] theory-solving 0 basic# ; #2024
[mk-app] #2025 = #2024 #2018
[instance] 0 #2025
[attach-enode] #2025 0
[end-of-instance]
[mk-app] #2024 or #1207 #201 #1307
[mk-app] #2025 or #2018 #1307
[inst-discovered] theory-solving 0 basic# ; #2025
[mk-app] #2026 = #2025 #2024
[instance] 0 #2026
[attach-enode] #2026 0
[end-of-instance]
[mk-quant] #2025 internal_the_q!model.gcd_nat.?_pre_post_definition 2 #1295 #2024
[attach-var-names] #2025 (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #2018 or #2016 #1207
[mk-app] #2023 not #2018
[inst-discovered] theory-solving 0 basic# ; #1274
[mk-app] #2026 = #1274 #2023
[instance] 0 #2026
[attach-enode] #2026 0
[end-of-instance]
[mk-app] #2026 not #2023
[inst-discovered] theory-solving 0 basic# ; #2026
[mk-app] #2027 = #2026 #2018
[instance] 0 #2027
[attach-enode] #2027 0
[end-of-instance]
[mk-app] #2026 or #2016 #1207 #1313
[mk-app] #2027 or #2018 #1313
[inst-discovered] theory-solving 0 basic# ; #2027
[mk-app] #2028 = #2027 #2026
[instance] 0 #2028
[attach-enode] #2028 0
[end-of-instance]
[mk-quant] #2027 internal_the_q!model.rec__gcd_nat.?_pre_post_rec_definition 3 #1271 #2026
[attach-var-names] #2027 (|fuel%| ; |Fuel|) (|b!| ; |Poly|) (|a!| ; |Poly|)
[mk-app] #2018 not #1410
[mk-app] #2023 not #1412
[mk-app] #2028 or #2018 #2023
[mk-app] #2029 not #2028
[inst-discovered] theory-solving 0 basic# ; #1413
[mk-app] #2030 = #1413 #2029
[instance] 0 #2030
[attach-enode] #2030 0
[end-of-instance]
[mk-app] #2030 = #2028 #1398
[mk-app] #2031 not #2030
[mk-app] #2032 = #1398 #2029
[inst-discovered] theory-solving 0 basic# ; #2032
[mk-app] #2033 = #2032 #2031
[instance] 0 #2033
[attach-enode] #2033 0
[end-of-instance]
[mk-app] #2029 not #2028
[inst-discovered] theory-solving 0 basic# ; #2031
[mk-app] #2029 = #2031 #2031
[instance] 0 #2029
[attach-enode] #2029 0
[end-of-instance]
[mk-quant] #2029 internal_the_q!model.fits_budget.?_definition 2 #1405 #2031
[attach-var-names] #2029 (|d!| ; |Poly|) (|n!| ; |Poly|)
[mk-app] #2032 or #1416 #2029
[mk-app] #2033 not #1441
[mk-app] #2034 not #1459
[mk-app] #2035 not #1460
[mk-app] #2036 not #1464
[mk-app] #2037 or #1456 #2033 #2034 #2035 #2036
[mk-app] #2038 not #2037
[inst-discovered] theory-solving 0 basic# ; #1465
[mk-app] #2039 = #1465 #2038
[instance] 0 #2039
[attach-enode] #2039 0
[end-of-instance]
[mk-app] #2039 = #2037 #1436
[mk-app] #2040 not #2039
[mk-app] #2041 = #1436 #2038
[inst-discovered] theory-solving 0 basic# ; #2041
[mk-app] #2042 = #2041 #2040
[instance] 0 #2042
[attach-enode] #2042 0
[end-of-instance]
[mk-app] #2038 not #2037
[inst-discovered] theory-solving 0 basic# ; #2040
[mk-app] #2038 = #2040 #2040
[instance] 0 #2038
[attach-enode] #2038 0
[end-of-instance]
[mk-quant] #2038 internal_the_q!model.impl&__0.wf.?_definition 1 #1453 #2040
[attach-var-names] #2038 (|self!| ; |Poly|)
[mk-app] #2041 or #1468 #2038
[mk-app] #2042 not #1527
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #2042 = #1530 #1530
[instance] 0 #2042
[attach-enode] #2042 0
[end-of-instance]
[mk-app] #2042 or #1967 #1968 #1969
[mk-app] #2043 not #2042
[inst-discovered] theory-solving 0 basic# ; #1057
[mk-app] #2044 = #1057 #2043
[instance] 0 #2044
[attach-enode] #2044 0
[end-of-instance]
[mk-app] #2044 not #2043
[inst-discovered] theory-solving 0 basic# ; #2044
[mk-app] #2045 = #2044 #2042
[instance] 0 #2045
[attach-enode] #2045 0
[end-of-instance]
[mk-app] #2044 or #1967 #1968 #1969 #1670
[mk-app] #2045 or #2042 #1670
[inst-discovered] theory-solving 0 basic# ; #2045
[mk-app] #2046 = #2045 #2044
[instance] 0 #2046
[attach-enode] #2046 0
[end-of-instance]
[mk-quant] #2045 internal_core__ops__function__impls__impl&__2_trait_impl_definition 4 #1672 #2044
[attach-var-names] #2045 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #2042 or #1967 #1968 #1969
[mk-app] #2043 not #2042
[inst-discovered] theory-solving 0 basic# ; #1057
[mk-app] #2046 = #1057 #2043
[instance] 0 #2046
[attach-enode] #2046 0
[end-of-instance]
[mk-app] #2046 not #2043
[inst-discovered] theory-solving 0 basic# ; #2046
[mk-app] #2047 = #2046 #2042
[instance] 0 #2047
[attach-enode] #2047 0
[end-of-instance]
[mk-app] #2046 or #1967 #1968 #1969 #1676
[mk-app] #2047 or #2042 #1676
[inst-discovered] theory-solving 0 basic# ; #2047
[mk-app] #2048 = #2047 #2046
[instance] 0 #2048
[attach-enode] #2048 0
[end-of-instance]
[mk-quant] #2047 internal_core__ops__function__impls__impl&__1_trait_impl_definition 4 #1678 #2046
[attach-var-names] #2047 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #2042 or #1967 #1968 #1969
[mk-app] #2043 not #2042
[inst-discovered] theory-solving 0 basic# ; #1057
[mk-app] #2048 = #1057 #2043
[instance] 0 #2048
[attach-enode] #2048 0
[end-of-instance]
[mk-app] #2048 not #2043
[inst-discovered] theory-solving 0 basic# ; #2048
[mk-app] #2049 = #2048 #2042
[instance] 0 #2049
[attach-enode] #2049 0
[end-of-instance]
[mk-app] #2048 or #1967 #1968 #1969 #1682
[mk-app] #2049 or #2042 #1682
[inst-discovered] theory-solving 0 basic# ; #2049
[mk-app] #2050 = #2049 #2048
[instance] 0 #2050
[attach-enode] #2050 0
[end-of-instance]
[mk-quant] #2049 internal_core__ops__function__impls__impl&__0_trait_impl_definition 4 #1684 #2048
[attach-var-names] #2049 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #2042 or #1971 #1950 #1976 #1981 #1721
[mk-app] #2043 not #2042
[inst-discovered] theory-solving 0 basic# ; #1098
[mk-app] #2050 = #1098 #2043
[instance] 0 #2050
[attach-enode] #2050 0
[end-of-instance]
[mk-app] #2050 not #2043
[inst-discovered] theory-solving 0 basic# ; #2050
[mk-app] #2051 = #2050 #2042
[instance] 0 #2051
[attach-enode] #2051 0
[end-of-instance]
[mk-app] #2050 or #1971 #1950 #1976 #1981 #1721 #1688
[mk-app] #2051 or #2042 #1688
[inst-discovered] theory-solving 0 basic# ; #2051
[mk-app] #2052 = #2051 #2050
[instance] 0 #2052
[attach-enode] #2052 0
[end-of-instance]
[mk-quant] #2051 internal_alloc__boxed__impl&__31_trait_impl_definition 6 #1690 #2050
[attach-var-names] #2051 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #2042 or #1971 #1950 #1976 #1992 #1721
[mk-app] #2043 not #2042
[inst-discovered] theory-solving 0 basic# ; #1694
[mk-app] #2052 = #1694 #2043
[instance] 0 #2052
[attach-enode] #2052 0
[end-of-instance]
[mk-app] #2052 not #2043
[inst-discovered] theory-solving 0 basic# ; #2052
[mk-app] #2053 = #2052 #2042
[instance] 0 #2053
[attach-enode] #2053 0
[end-of-instance]
[mk-app] #2052 or #1971 #1950 #1976 #1992 #1721 #1695
[mk-app] #2053 or #2042 #1695
[inst-discovered] theory-solving 0 basic# ; #2053
[mk-app] #2054 = #2053 #2052
[instance] 0 #2054
[attach-enode] #2054 0
[end-of-instance]
[mk-quant] #2053 internal_alloc__boxed__impl&__32_trait_impl_definition 6 #1697 #2052
[attach-var-names] #2053 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #2042 not #1702
[mk-app] #2043 or #1971 #1950 #1976 #2042 #1721
[mk-app] #2054 not #2043
[inst-discovered] theory-solving 0 basic# ; #1703
[mk-app] #2055 = #1703 #2054
[instance] 0 #2055
[attach-enode] #2055 0
[end-of-instance]
[mk-app] #2055 not #2054
[inst-discovered] theory-solving 0 basic# ; #2055
[mk-app] #2056 = #2055 #2043
[instance] 0 #2056
[attach-enode] #2056 0
[end-of-instance]
[mk-app] #2055 or #1971 #1950 #1976 #2042 #1721 #1704
[mk-app] #2056 or #2043 #1704
[inst-discovered] theory-solving 0 basic# ; #2056
[mk-app] #2057 = #2056 #2055
[instance] 0 #2057
[attach-enode] #2057 0
[end-of-instance]
[mk-quant] #2056 internal_alloc__boxed__impl&__33_trait_impl_definition 6 #1706 #2055
[attach-var-names] #2056 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|F&| ; |Type|) (|F&.| ; |Dcr|) (|Args&| ; |Type|) (|Args&.| ; |Dcr|)
[mk-app] #2043 or #1967 #1968 #1970
[mk-app] #2054 not #2043
[inst-discovered] theory-solving 0 basic# ; #1077
[mk-app] #2057 = #1077 #2054
[instance] 0 #2057
[attach-enode] #2057 0
[end-of-instance]
[mk-app] #2057 not #2054
[inst-discovered] theory-solving 0 basic# ; #2057
[mk-app] #2058 = #2057 #2043
[instance] 0 #2058
[attach-enode] #2058 0
[end-of-instance]
[mk-app] #2057 or #1967 #1968 #1970 #1711
[mk-app] #2058 or #2043 #1711
[inst-discovered] theory-solving 0 basic# ; #2058
[mk-app] #2059 = #2058 #2057
[instance] 0 #2059
[attach-enode] #2059 0
[end-of-instance]
[mk-quant] #2058 internal_core__ops__function__impls__impl&__3_trait_impl_definition 4 #1713 #2057
[attach-var-names] #2058 (|F&| ; |Type|) (|F&.| ; |Dcr|) (|A&| ; |Type|) (|A&.| ; |Dcr|)
[mk-app] #2043 not #1730
[mk-app] #2054 or #1950 #2043 #1721
[mk-app] #2059 not #2054
[inst-discovered] theory-solving 0 basic# ; #1731
[mk-app] #2060 = #1731 #2059
[instance] 0 #2060
[attach-enode] #2060 0
[end-of-instance]
[mk-app] #2060 not #2059
[inst-discovered] theory-solving 0 basic# ; #2060
[mk-app] #2061 = #2060 #2054
[instance] 0 #2061
[attach-enode] #2061 0
[end-of-instance]
[mk-app] #2060 or #1950 #2043 #1721 #1732
[mk-app] #2061 or #2054 #1732
[inst-discovered] theory-solving 0 basic# ; #2061
[mk-app] #2062 = #2061 #2060
[instance] 0 #2062
[attach-enode] #2062 0
[end-of-instance]
[mk-quant] #2061 internal_alloc__boxed__impl&__49_trait_impl_definition 4 #1734 #2060
[attach-var-names] #2061 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #2054 or #1950 #2043 #1721
[mk-app] #2059 not #2054
[inst-discovered] theory-solving 0 basic# ; #1731
[mk-app] #2062 = #1731 #2059
[instance] 0 #2062
[attach-enode] #2062 0
[end-of-instance]
[mk-app] #2062 not #2059
[inst-discovered] theory-solving 0 basic# ; #2062
[mk-app] #2063 = #2062 #2054
[instance] 0 #2063
[attach-enode] #2063 0
[end-of-instance]
[mk-app] #2062 or #1950 #2043 #1721 #1740
[mk-app] #2063 or #2054 #1740
[inst-discovered] theory-solving 0 basic# ; #2063
[mk-app] #2064 = #2063 #2062
[instance] 0 #2064
[attach-enode] #2064 0
[end-of-instance]
[mk-quant] #2063 internal_alloc__rc__impl&__115_trait_impl_definition 4 #1742 #2062
[attach-var-names] #2063 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #2054 or #1950 #2043 #1721
[mk-app] #2059 not #2054
[inst-discovered] theory-solving 0 basic# ; #1731
[mk-app] #2064 = #1731 #2059
[instance] 0 #2064
[attach-enode] #2064 0
[end-of-instance]
[mk-app] #2064 not #2059
[inst-discovered] theory-solving 0 basic# ; #2064
[mk-app] #2065 = #2064 #2054
[instance] 0 #2065
[attach-enode] #2065 0
[end-of-instance]
[mk-app] #2064 or #1950 #2043 #1721 #1747
[mk-app] #2065 or #2054 #1747
[inst-discovered] theory-solving 0 basic# ; #2065
[mk-app] #2066 = #2065 #2064
[instance] 0 #2066
[attach-enode] #2066 0
[end-of-instance]
[mk-quant] #2065 internal_alloc__sync__impl&__117_trait_impl_definition 4 #1749 #2064
[attach-var-names] #2065 (|A&| ; |Type|) (|A&.| ; |Dcr|) (|T&| ; |Type|) (|T&.| ; |Dcr|)
[mk-app] #2054 not #1759
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #2054 = #1762 #1762
[instance] 0 #2054
[attach-enode] #2054 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1807
[mk-app] #1736 = #1807 #1807
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1819
[mk-app] #1736 = #1819 #1819
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1822
[mk-app] #1736 = #1822 #1822
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1826
[mk-app] #1736 = #1826 #1826
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1829
[mk-app] #1736 = #1829 #1829
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1832
[mk-app] #1736 = #1832 #1832
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1836
[mk-app] #1736 = #1836 #1836
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1840
[mk-app] #1736 = #1840 #1840
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1844
[mk-app] #1736 = #1844 #1844
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1854
[inst-discovered] theory-solving 0 basic# ; #1857
[mk-app] #1736 = #1857 #1857
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1855
[inst-discovered] theory-solving 0 basic# ; #1861
[mk-app] #1736 = #1861 #1861
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1840
[mk-app] #1736 = #1840 #1840
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1844
[mk-app] #1736 = #1844 #1844
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1866
[mk-app] #1736 = #1866 #1866
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1872
[mk-app] #1736 = #1872 #1872
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1877
[mk-app] #1736 = #1877 #1877
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1882
[mk-app] #1736 = #1882 #1882
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1886
[mk-app] #1736 = #1886 #1886
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1888
[mk-app] #1736 = #1888 #1888
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1890
[mk-app] #1736 = #1890 #1890
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1892
[mk-app] #1736 = #1892 #1892
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1894
[mk-app] #1736 = #1894 #1894
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1896
[mk-app] #1736 = #1896 #1896
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1898
[mk-app] #1736 = #1898 #1898
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1901
[mk-app] #1736 = #1901 #1901
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1903
[mk-app] #1736 = #1903 #1903
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1906
[inst-discovered] theory-solving 0 basic# ; #1909
[mk-app] #1736 = #1909 #1909
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1911
[inst-discovered] theory-solving 0 basic# ; #1914
[mk-app] #1736 = #1914 #1914
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1917
[mk-app] #1736 = #1917 #1917
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1945
[mk-app] #1736 = #1945 #1945
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #914
[mk-app] #1736 = #914 #914
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #919
[mk-app] #1736 = #919 #919
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1952
[mk-app] #1736 = #1952 #1952
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1959
[mk-app] #1736 = #1959 #1959
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1963
[mk-app] #1736 = #1963 #1963
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1984
[mk-app] #1736 = #1984 #1984
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1986
[mk-app] #1736 = #1986 #1986
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1995
[mk-app] #1736 = #1995 #1995
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2008
[mk-app] #1736 = #2008 #2008
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2010
[mk-app] #1736 = #2010 #2010
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2019
[mk-app] #1736 = #2019 #2019
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2021
[mk-app] #1736 = #2021 #2021
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2024
[mk-app] #1736 = #2024 #2024
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2026
[mk-app] #1736 = #2026 #2026
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2028
[mk-app] #1736 = #2028 #2028
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #2028
[inst-discovered] theory-solving 0 basic# ; #2031
[mk-app] #1736 = #2031 #2031
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2037
[mk-app] #1736 = #2037 #2037
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #2037
[inst-discovered] theory-solving 0 basic# ; #2040
[mk-app] #1736 = #2040 #2040
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1527
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #1736 = #1530 #1530
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2050
[mk-app] #1736 = #2050 #2050
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2052
[mk-app] #1736 = #2052 #2052
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2055
[mk-app] #1736 = #2055 #2055
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2060
[mk-app] #1736 = #2060 #2060
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2062
[mk-app] #1736 = #2062 #2062
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2064
[mk-app] #1736 = #2064 #2064
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1759
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #1736 = #1762 #1762
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1807
[mk-app] #1736 = #1807 #1807
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1819
[mk-app] #1736 = #1819 #1819
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1822
[mk-app] #1736 = #1822 #1822
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1826
[mk-app] #1736 = #1826 #1826
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1829
[mk-app] #1736 = #1829 #1829
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1832
[mk-app] #1736 = #1832 #1832
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1836
[mk-app] #1736 = #1836 #1836
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1840
[mk-app] #1736 = #1840 #1840
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1844
[mk-app] #1736 = #1844 #1844
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1854
[inst-discovered] theory-solving 0 basic# ; #1857
[mk-app] #1736 = #1857 #1857
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1855
[inst-discovered] theory-solving 0 basic# ; #1861
[mk-app] #1736 = #1861 #1861
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1840
[mk-app] #1736 = #1840 #1840
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1844
[mk-app] #1736 = #1844 #1844
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1866
[mk-app] #1736 = #1866 #1866
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1872
[mk-app] #1736 = #1872 #1872
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1877
[mk-app] #1736 = #1877 #1877
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1882
[mk-app] #1736 = #1882 #1882
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1886
[mk-app] #1736 = #1886 #1886
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1888
[mk-app] #1736 = #1888 #1888
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1890
[mk-app] #1736 = #1890 #1890
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1892
[mk-app] #1736 = #1892 #1892
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1894
[mk-app] #1736 = #1894 #1894
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1896
[mk-app] #1736 = #1896 #1896
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1898
[mk-app] #1736 = #1898 #1898
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1901
[mk-app] #1736 = #1901 #1901
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1903
[mk-app] #1736 = #1903 #1903
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1906
[inst-discovered] theory-solving 0 basic# ; #1909
[mk-app] #1736 = #1909 #1909
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1911
[inst-discovered] theory-solving 0 basic# ; #1914
[mk-app] #1736 = #1914 #1914
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #914
[mk-app] #1736 = #914 #914
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #919
[mk-app] #1736 = #919 #919
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1952
[mk-app] #1736 = #1952 #1952
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1959
[mk-app] #1736 = #1959 #1959
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1963
[mk-app] #1736 = #1963 #1963
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1984
[mk-app] #1736 = #1984 #1984
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1986
[mk-app] #1736 = #1986 #1986
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #1995
[mk-app] #1736 = #1995 #1995
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2008
[mk-app] #1736 = #2008 #2008
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2010
[mk-app] #1736 = #2010 #2010
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2019
[mk-app] #1736 = #2019 #2019
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2021
[mk-app] #1736 = #2021 #2021
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2024
[mk-app] #1736 = #2024 #2024
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2026
[mk-app] #1736 = #2026 #2026
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2028
[mk-app] #1736 = #2028 #2028
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #2028
[inst-discovered] theory-solving 0 basic# ; #2031
[mk-app] #1736 = #2031 #2031
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2037
[mk-app] #1736 = #2037 #2037
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #2037
[inst-discovered] theory-solving 0 basic# ; #2040
[mk-app] #1736 = #2040 #2040
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1527
[inst-discovered] theory-solving 0 basic# ; #1530
[mk-app] #1736 = #1530 #1530
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2050
[mk-app] #1736 = #2050 #2050
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2052
[mk-app] #1736 = #2052 #2052
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2055
[mk-app] #1736 = #2055 #2055
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2060
[mk-app] #1736 = #2060 #2060
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2062
[mk-app] #1736 = #2062 #2062
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2064
[mk-app] #1736 = #2064 #2064
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 not #1759
[inst-discovered] theory-solving 0 basic# ; #1762
[mk-app] #1736 = #1762 #1762
[instance] 0 #1736
[attach-enode] #1736 0
[end-of-instance]
[mk-app] #1736 or #878 #874
[mk-app] #1751 or #878 #875
[mk-app] #1752 or #908 #881
[mk-app] #1744 or #908 #882
[mk-app] #1745 or #908 #883
[mk-app] #1737 or #908 #884
[mk-app] #1738 or #908 #885
[mk-app] #1083 or #908 #886
[mk-app] #1715 or #908 #887
[mk-app] #1716 or #908 #888
[mk-app] #1708 or #908 #889
[mk-app] #1709 or #908 #890
[mk-app] #1710 or #908 #891
[mk-app] #1699 or #908 #892
[mk-app] #1700 or #908 #893
[mk-app] #1701 or #908 #894
[mk-app] #1106 or #908 #895
[mk-app] #1692 or #908 #896
[mk-app] #1693 or #908 #897
[mk-app] #1065 or #908 #898
[mk-app] #1686 or #908 #899
[mk-app] #1687 or #908 #900
[mk-app] #1680 or #908 #901
[mk-app] #1681 or #908 #902
[mk-app] #1674 or #908 #903
[mk-app] #1675 or #908 #904
[mk-app] #1457 or #908 #905
[assign] #39 justification -1: 
[assign] #43 justification -1: 
[assign] #56 justification -1: 
[assign] #63 justification -1: 
[assign] #1808 justification -1: 
[assign] #88 justification -1: 
[assign] #92 justification -1: 
[assign] #96 justification -1: 
[assign] #100 justification -1: 
[assign] #104 justification -1: 
[assign] #108 justification -1: 
[assign] #112 justification -1: 
[assign] #116 justification -1: 
[assign] #120 justification -1: 
[attach-enode] #121 0
[attach-enode] #122 0
[assign] #122 justification -1: 
[assign] #128 justification -1: 
[assign] #134 justification -1: 
[assign] #139 justification -1: 
[assign] #144 justification -1: 
[assign] #1811 justification -1: 
[assign] #161 justification -1: 
[assign] #165 justification -1: 
[assign] #170 justification -1: 
[assign] #174 justification -1: 
[assign] #184 justification -1: 
[assign] #195 justification -1: 
[assign] #203 justification -1: 
[assign] #211 justification -1: 
[assign] #219 justification -1: 
[assign] #228 justification -1: 
[assign] #236 justification -1: 
[assign] #244 justification -1: 
[assign] #252 justification -1: 
[assign] #262 justification -1: 
[assign] #269 justification -1: 
[attach-enode] #270 0
[attach-enode] #271 0
[attach-enode] #272 0
[attach-enode] #273 0
[attach-enode] #274 0
[attach-enode] #276 0
[attach-enode] #277 0
[attach-enode] #278 0
[attach-enode] #279 0
[assign] #279 justification -1: 
[attach-enode] #280 0
[attach-enode] #281 0
[attach-enode] #282 0
[attach-enode] #283 0
[assign] #283 justification -1: 
[attach-enode] #284 0
[attach-enode] #285 0
[attach-enode] #286 0
[assign] #286 justification -1: 
[attach-enode] #287 0
[attach-enode] #288 0
[attach-enode] #289 0
[assign] #289 justification -1: 
[attach-enode] #290 0
[attach-enode] #291 0
[attach-enode] #296 0
[attach-enode] #297 0
[assign] #297 justification -1: 
[attach-enode] #298 0
[attach-enode] #301 0
[attach-enode] #302 0
[assign] #302 justification -1: 
[attach-enode] #303 0
[attach-enode] #307 0
[attach-enode] #308 0
[assign] #308 justification -1: 
[attach-enode] #309 0
[attach-enode] #313 0
[attach-enode] #314 0
[assign] #314 justification -1: 
[attach-enode] #315 0
[attach-enode] #319 0
[attach-enode] #320 0
[assign] #320 justification -1: 
[attach-enode] #321 0
[attach-enode] #325 0
[attach-enode] #326 0
[assign] #326 justification -1: 
[attach-enode] #327 0
[attach-enode] #328 0
[assign] #328 justification -1: 
[attach-enode] #329 0
[attach-enode] #304 0
[attach-enode] #330 0
[assign] #330 justification -1: 
[attach-enode] #331 0
[attach-enode] #310 0
[attach-enode] #332 0
[assign] #332 justification -1: 
[attach-enode] #333 0
[attach-enode] #316 0
[attach-enode] #334 0
[assign] #334 justification -1: 
[attach-enode] #335 0
[attach-enode] #322 0
[attach-enode] #336 0
[assign] #336 justification -1: 
[assign] #1816 justification -1: 
[assign] #1824 justification -1: 
[assign] #1831 justification -1: 
[assign] #1853 justification -1: 
[assign] #1858 justification -1: 
[assign] #1862 justification -1: 
[assign] #1863 justification -1: 
[assign] #463 justification -1: 
[assign] #469 justification -1: 
[assign] #477 justification -1: 
[assign] #485 justification -1: 
[assign] #492 justification -1: 
[assign] #499 justification -1: 
[assign] #505 justification -1: 
[assign] #512 justification -1: 
[assign] #518 justification -1: 
[assign] #523 justification -1: 
[assign] #528 justification -1: 
[assign] #533 justification -1: 
[assign] #538 justification -1: 
[assign] #542 justification -1: 
[assign] #548 justification -1: 
[assign] #563 justification -1: 
[assign] #570 justification -1: 
[assign] #579 justification -1: 
[assign] #588 justification -1: 
[assign] #594 justification -1: 
[assign] #611 justification -1: 
[assign] #618 justification -1: 
[assign] #627 justification -1: 
[assign] #1865 justification -1: 
[assign] #1873 justification -1: 
[assign] #1878 justification -1: 
[assign] #1883 justification -1: 
[assign] #1887 justification -1: 
[assign] #1889 justification -1: 
[assign] #1891 justification -1: 
[assign] #1893 justification -1: 
[assign] #1895 justification -1: 
[assign] #1885 justification -1: 
[assign] #1897 justification -1: 
[assign] #756 justification -1: 
[assign] #1905 justification -1: 
[assign] #1907 justification -1: 
[assign] #1912 justification -1: 
[mk-app] #1947 distinct-aux-f!!2 #792
[mk-app] #1919 unique-value!3
[attach-enode] #1919 0
[mk-app] #1465 = #1947 #1919
[attach-enode] #792 0
[attach-enode] #1947 0
[attach-enode] #1465 0
[assign] #1465 justification -1: 
[mk-app] #1466 distinct-aux-f!!2 #793
[mk-app] #1467 unique-value!4
[attach-enode] #1467 0
[mk-app] #1469 = #1466 #1467
[attach-enode] #793 0
[attach-enode] #1466 0
[attach-enode] #1469 0
[assign] #1469 justification -1: 
[mk-app] #1413 distinct-aux-f!!2 #794
[mk-app] #1414 unique-value!5
[attach-enode] #1414 0
[mk-app] #1415 = #1413 #1414
[attach-enode] #794 0
[attach-enode] #1413 0
[attach-enode] #1415 0
[assign] #1415 justification -1: 
[mk-app] #1417 distinct-aux-f!!2 #795
[mk-app] #1284 unique-value!6
[attach-enode] #1284 0
[mk-app] #1312 = #1417 #1284
[attach-enode] #795 0
[attach-enode] #1417 0
[attach-enode] #1312 0
[assign] #1312 justification -1: 
[mk-app] #1314 distinct-aux-f!!2 #796
[mk-app] #1298 unique-value!7
[attach-enode] #1298 0
[mk-app] #1306 = #1314 #1298
[attach-enode] #796 0
[attach-enode] #1314 0
[attach-enode] #1306 0
[assign] #1306 justification -1: 
[mk-app] #1308 distinct-aux-f!!2 #797
[mk-app] #1299 unique-value!8
[attach-enode] #1299 0
[mk-app] #1300 = #1308 #1299
[attach-enode] #797 0
[attach-enode] #1308 0
[attach-enode] #1300 0
[assign] #1300 justification -1: 
[mk-app] #1302 distinct-aux-f!!2 #798
[mk-app] #1285 unique-value!9
[attach-enode] #1285 0
[mk-app] #1286 = #1302 #1285
[attach-enode] #798 0
[attach-enode] #1302 0
[attach-enode] #1286 0
[assign] #1286 justification -1: 
[mk-app] #1801 distinct-aux-f!!2 #799
[mk-app] #1802 unique-value!10
[attach-enode] #1802 0
[mk-app] #1803 = #1801 #1802
[attach-enode] #799 0
[attach-enode] #1801 0
[attach-enode] #1803 0
[assign] #1803 justification -1: 
[mk-app] #1179 distinct-aux-f!!2 #800
[mk-app] #1176 unique-value!11
[attach-enode] #1176 0
[mk-app] #1177 = #1179 #1176
[attach-enode] #800 0
[attach-enode] #1179 0
[attach-enode] #1177 0
[assign] #1177 justification -1: 
[mk-app] #1180 distinct-aux-f!!2 #801
[mk-app] #1178 unique-value!12
[attach-enode] #1178 0
[mk-app] #1182 = #1180 #1178
[attach-enode] #801 0
[attach-enode] #1180 0
[attach-enode] #1182 0
[assign] #1182 justification -1: 
[mk-app] #1144 distinct-aux-f!!2 #802
[mk-app] #1141 unique-value!13
[attach-enode] #1141 0
[mk-app] #1142 = #1144 #1141
[attach-enode] #802 0
[attach-enode] #1144 0
[attach-enode] #1142 0
[assign] #1142 justification -1: 
[mk-app] #1145 distinct-aux-f!!2 #803
[mk-app] #1143 unique-value!14
[attach-enode] #1143 0
[mk-app] #1147 = #1145 #1143
[attach-enode] #803 0
[attach-enode] #1145 0
[attach-enode] #1147 0
[assign] #1147 justification -1: 
[mk-app] #1121 distinct-aux-f!!2 #804
[mk-app] #1122 unique-value!15
[attach-enode] #1122 0
[mk-app] #1115 = #1121 #1122
[attach-enode] #804 0
[attach-enode] #1121 0
[attach-enode] #1115 0
[assign] #1115 justification -1: 
[mk-app] #1116 distinct-aux-f!!2 #805
[mk-app] #1107 unique-value!16
[attach-enode] #1107 0
[mk-app] #1108 = #1116 #1107
[attach-enode] #805 0
[attach-enode] #1116 0
[attach-enode] #1108 0
[assign] #1108 justification -1: 
[mk-app] #1091 distinct-aux-f!!2 #806
[mk-app] #1092 unique-value!17
[attach-enode] #1092 0
[mk-app] #1084 = #1091 #1092
[attach-enode] #806 0
[attach-enode] #1091 0
[attach-enode] #1084 0
[assign] #1084 justification -1: 
[mk-app] #1085 distinct-aux-f!!2 #807
[mk-app] #1074 unique-value!18
[attach-enode] #1074 0
[mk-app] #1075 = #1085 #1074
[attach-enode] #807 0
[attach-enode] #1085 0
[attach-enode] #1075 0
[assign] #1075 justification -1: 
[mk-app] #1066 distinct-aux-f!!2 #808
[mk-app] #1067 unique-value!19
[attach-enode] #1067 0
[mk-app] #1049 = #1066 #1067
[attach-enode] #808 0
[attach-enode] #1066 0
[attach-enode] #1049 0
[assign] #1049 justification -1: 
[mk-app] #1050 distinct-aux-f!!2 #809
[mk-app] #1041 unique-value!20
[attach-enode] #1041 0
[mk-app] #1042 = #1050 #1041
[attach-enode] #809 0
[attach-enode] #1050 0
[attach-enode] #1042 0
[assign] #1042 justification -1: 
[mk-app] #1033 distinct-aux-f!!2 #810
[mk-app] #1034 unique-value!21
[attach-enode] #1034 0
[mk-app] #973 = #1033 #1034
[attach-enode] #810 0
[attach-enode] #1033 0
[attach-enode] #973 0
[assign] #973 justification -1: 
[mk-app] #974 distinct-aux-f!!2 #811
[mk-app] #975 unique-value!22
[attach-enode] #975 0
[mk-app] #909 = #974 #975
[attach-enode] #811 0
[attach-enode] #974 0
[attach-enode] #909 0
[assign] #909 justification -1: 
[mk-app] #879 distinct-aux-f!!2 #812
[mk-app] #780 unique-value!23
[attach-enode] #780 0
[mk-app] #781 = #879 #780
[attach-enode] #812 0
[attach-enode] #879 0
[attach-enode] #781 0
[assign] #781 justification -1: 
[mk-app] #782 distinct-aux-f!!2 #813
[mk-app] #783 unique-value!24
[attach-enode] #783 0
[mk-app] #744 = #782 #783
[attach-enode] #813 0
[attach-enode] #782 0
[attach-enode] #744 0
[assign] #744 justification -1: 
[mk-app] #745 distinct-aux-f!!2 #814
[mk-app] #746 unique-value!25
[attach-enode] #746 0
[mk-app] #747 = #745 #746
[attach-enode] #814 0
[attach-enode] #745 0
[attach-enode] #747 0
[assign] #747 justification -1: 
[mk-app] #733 distinct-aux-f!!2 #815
[mk-app] #735 unique-value!26
[attach-enode] #735 0
[mk-app] #736 = #733 #735
[attach-enode] #815 0
[attach-enode] #733 0
[attach-enode] #736 0
[assign] #736 justification -1: 
[mk-app] #737 distinct-aux-f!!2 #816
[mk-app] #692 unique-value!27
[attach-enode] #692 0
[mk-app] #723 = #737 #692
[attach-enode] #816 0
[attach-enode] #737 0
[attach-enode] #723 0
[assign] #723 justification -1: 
[mk-app] #724 distinct-aux-f!!2 #817
[mk-app] #681 unique-value!28
[attach-enode] #681 0
[mk-app] #716 = #724 #681
[attach-enode] #817 0
[attach-enode] #724 0
[attach-enode] #716 0
[assign] #716 justification -1: 
[mk-app] #717 distinct-aux-f!!2 #818
[mk-app] #708 unique-value!29
[attach-enode] #708 0
[mk-app] #709 = #717 #708
[attach-enode] #818 0
[attach-enode] #717 0
[attach-enode] #709 0
[assign] #709 justification -1: 
[mk-app] #701 distinct-aux-f!!2 #819
[mk-app] #702 unique-value!30
[attach-enode] #702 0
[mk-app] #693 = #701 #702
[attach-enode] #819 0
[attach-enode] #701 0
[attach-enode] #693 0
[assign] #693 justification -1: 
[mk-app] #694 distinct-aux-f!!2 #820
[mk-app] #682 unique-value!31
[attach-enode] #682 0
[mk-app] #683 = #694 #682
[attach-enode] #820 0
[attach-enode] #694 0
[attach-enode] #683 0
[assign] #683 justification -1: 
[mk-app] #647 distinct-aux-f!!2 #821
[mk-app] #648 unique-value!32
[attach-enode] #648 0
[mk-app] #654 = #647 #648
[attach-enode] #821 0
[attach-enode] #647 0
[attach-enode] #654 0
[assign] #654 justification -1: 
[mk-app] #668 distinct-aux-f!!2 #822
[mk-app] #669 unique-value!33
[attach-enode] #669 0
[mk-app] #670 = #668 #669
[attach-enode] #822 0
[attach-enode] #668 0
[attach-enode] #670 0
[assign] #670 justification -1: 
[mk-app] #671 distinct-aux-f!!2 #823
[mk-app] #653 unique-value!34
[attach-enode] #653 0
[mk-app] #655 = #671 #653
[attach-enode] #823 0
[attach-enode] #671 0
[attach-enode] #655 0
[assign] #655 justification -1: 
[mk-app] #656 distinct-aux-f!!2 #824
[mk-app] #634 unique-value!35
[attach-enode] #634 0
[mk-app] #635 = #656 #634
[attach-enode] #824 0
[attach-enode] #656 0
[attach-enode] #635 0
[assign] #635 justification -1: 
[mk-app] #637 distinct-aux-f!!2 #825
[mk-app] #638 unique-value!36
[attach-enode] #638 0
[mk-app] #435 = #637 #638
[attach-enode] #825 0
[attach-enode] #637 0
[attach-enode] #435 0
[assign] #435 justification -1: 
[mk-app] #436 distinct-aux-f!!2 #826
[mk-app] #437 unique-value!37
[attach-enode] #437 0
[mk-app] #459 = #436 #437
[attach-enode] #826 0
[attach-enode] #436 0
[attach-enode] #459 0
[assign] #459 justification -1: 
[mk-app] #460 distinct-aux-f!!2 #827
[mk-app] #405 unique-value!38
[attach-enode] #405 0
[mk-app] #407 = #460 #405
[attach-enode] #827 0
[attach-enode] #460 0
[attach-enode] #407 0
[assign] #407 justification -1: 
[mk-app] #455 distinct-aux-f!!2 #828
[mk-app] #456 unique-value!39
[attach-enode] #456 0
[mk-app] #374 = #455 #456
[attach-enode] #828 0
[attach-enode] #455 0
[attach-enode] #374 0
[assign] #374 justification -1: 
[mk-app] #376 distinct-aux-f!!2 #829
[mk-app] #449 unique-value!40
[attach-enode] #449 0
[mk-app] #450 = #376 #449
[attach-enode] #829 0
[attach-enode] #376 0
[attach-enode] #450 0
[assign] #450 justification -1: 
[mk-app] #430 distinct-aux-f!!2 #830
[mk-app] #432 unique-value!41
[attach-enode] #432 0
[mk-app] #433 = #430 #432
[attach-enode] #830 0
[attach-enode] #430 0
[attach-enode] #433 0
[assign] #433 justification -1: 
[mk-app] #439 distinct-aux-f!!2 #831
[mk-app] #440 unique-value!42
[attach-enode] #440 0
[mk-app] #441 = #439 #440
[attach-enode] #831 0
[attach-enode] #439 0
[attach-enode] #441 0
[assign] #441 justification -1: 
[mk-app] #442 distinct-aux-f!!2 #832
[mk-app] #398 unique-value!43
[attach-enode] #398 0
[mk-app] #408 = #442 #398
[attach-enode] #832 0
[attach-enode] #442 0
[attach-enode] #408 0
[assign] #408 justification -1: 
[mk-app] #409 distinct-aux-f!!2 #833
[mk-app] #410 unique-value!44
[attach-enode] #410 0
[mk-app] #411 = #409 #410
[attach-enode] #833 0
[attach-enode] #409 0
[attach-enode] #411 0
[assign] #411 justification -1: 
[mk-app] #368 distinct-aux-f!!2 #834
[mk-app] #377 unique-value!45
[attach-enode] #377 0
[mk-app] #378 = #368 #377
[attach-enode] #834 0
[attach-enode] #368 0
[attach-enode] #378 0
[assign] #378 justification -1: 
[mk-app] #379 distinct-aux-f!!2 #835
[mk-app] #380 unique-value!46
[attach-enode] #380 0
[mk-app] #350 = #379 #380
[attach-enode] #835 0
[attach-enode] #379 0
[attach-enode] #350 0
[assign] #350 justification -1: 
[mk-app] #351 distinct-aux-f!!2 #836
[mk-app] #155 unique-value!47
[attach-enode] #155 0
[mk-app] #156 = #351 #155
[attach-enode] #836 0
[attach-enode] #351 0
[attach-enode] #156 0
[assign] #156 justification -1: 
[mk-app] #76 distinct-aux-f!!2 #837
[mk-app] #77 unique-value!48
[attach-enode] #77 0
[mk-app] #78 = #76 #77
[attach-enode] #837 0
[attach-enode] #76 0
[attach-enode] #78 0
[assign] #78 justification -1: 
[mk-app] #2054 distinct-aux-f!!2 #838
[mk-app] #2059 unique-value!49
[attach-enode] #2059 0
[mk-app] #2066 = #2054 #2059
[attach-enode] #838 0
[attach-enode] #2054 0
[attach-enode] #2066 0
[assign] #2066 justification -1: 
[mk-app] #2067 distinct-aux-f!!2 #839
[mk-app] #2068 unique-value!50
[attach-enode] #2068 0
[mk-app] #2069 = #2067 #2068
[attach-enode] #839 0
[attach-enode] #2067 0
[attach-enode] #2069 0
[assign] #2069 justification -1: 
[mk-app] #2070 distinct-aux-f!!2 #840
[mk-app] #2071 unique-value!51
[attach-enode] #2071 0
[mk-app] #2072 = #2070 #2071
[attach-enode] #840 0
[attach-enode] #2070 0
[attach-enode] #2072 0
[assign] #2072 justification -1: 
[mk-app] #2073 distinct-aux-f!!2 #841
[mk-app] #2074 unique-value!52
[attach-enode] #2074 0
[mk-app] #2075 = #2073 #2074
[attach-enode] #841 0
[attach-enode] #2073 0
[attach-enode] #2075 0
[assign] #2075 justification -1: 
[mk-app] #2076 distinct-aux-f!!2 #842
[mk-app] #2077 unique-value!53
[attach-enode] #2077 0
[mk-app] #2078 = #2076 #2077
[attach-enode] #842 0
[attach-enode] #2076 0
[attach-enode] #2078 0
[assign] #2078 justification -1: 
[mk-app] #2079 distinct-aux-f!!2 #843
[mk-app] #2080 unique-value!54
[attach-enode] #2080 0
[mk-app] #2081 = #2079 #2080
[attach-enode] #843 0
[attach-enode] #2079 0
[attach-enode] #2081 0
[assign] #2081 justification -1: 
[mk-app] #2082 distinct-aux-f!!2 #844
[mk-app] #2083 unique-value!55
[attach-enode] #2083 0
[mk-app] #2084 = #2082 #2083
[attach-enode] #844 0
[attach-enode] #2082 0
[attach-enode] #2084 0
[assign] #2084 justification -1: 
[mk-app] #2085 distinct-aux-f!!2 #845
[mk-app] #2086 unique-value!56
[attach-enode] #2086 0
[mk-app] #2087 = #2085 #2086
[attach-enode] #845 0
[attach-enode] #2085 0
[attach-enode] #2087 0
[assign] #2087 justification -1: 
[mk-app] #2088 distinct-aux-f!!2 #846
[mk-app] #2089 unique-value!57
[attach-enode] #2089 0
[mk-app] #2090 = #2088 #2089
[attach-enode] #846 0
[attach-enode] #2088 0
[attach-enode] #2090 0
[assign] #2090 justification -1: 
[mk-app] #2091 distinct-aux-f!!2 #847
[mk-app] #2092 unique-value!58
[attach-enode] #2092 0
[mk-app] #2093 = #2091 #2092
[attach-enode] #847 0
[attach-enode] #2091 0
[attach-enode] #2093 0
[assign] #2093 justification -1: 
[mk-app] #2094 distinct-aux-f!!2 #848
[mk-app] #2095 unique-value!59
[attach-enode] #2095 0
[mk-app] #2096 = #2094 #2095
[attach-enode] #848 0
[attach-enode] #2094 0
[attach-enode] #2096 0
[assign] #2096 justification -1: 
[mk-app] #2097 distinct-aux-f!!2 #849
[mk-app] #2098 unique-value!60
[attach-enode] #2098 0
[mk-app] #2099 = #2097 #2098
[attach-enode] #849 0
[attach-enode] #2097 0
[attach-enode] #2099 0
[assign] #2099 justification -1: 
[mk-app] #2100 distinct-aux-f!!2 #850
[mk-app] #2101 unique-value!61
[attach-enode] #2101 0
[mk-app] #2102 = #2100 #2101
[attach-enode] #850 0
[attach-enode] #2100 0
[attach-enode] #2102 0
[assign] #2102 justification -1: 
[mk-app] #2103 distinct-aux-f!!2 #851
[mk-app] #2104 unique-value!62
[attach-enode] #2104 0
[mk-app] #2105 = #2103 #2104
[attach-enode] #851 0
[attach-enode] #2103 0
[attach-enode] #2105 0
[assign] #2105 justification -1: 
[mk-app] #2106 distinct-aux-f!!2 #852
[mk-app] #2107 unique-value!63
[attach-enode] #2107 0
[mk-app] #2108 = #2106 #2107
[attach-enode] #852 0
[attach-enode] #2106 0
[attach-enode] #2108 0
[assign] #2108 justification -1: 
[mk-app] #2109 distinct-aux-f!!2 #853
[mk-app] #2110 unique-value!64
[attach-enode] #2110 0
[mk-app] #2111 = #2109 #2110
[attach-enode] #853 0
[attach-enode] #2109 0
[attach-enode] #2111 0
[assign] #2111 justification -1: 
[mk-app] #2112 distinct-aux-f!!2 #854
[mk-app] #2113 unique-value!65
[attach-enode] #2113 0
[mk-app] #2114 = #2112 #2113
[attach-enode] #854 0
[attach-enode] #2112 0
[attach-enode] #2114 0
[assign] #2114 justification -1: 
[mk-app] #2115 distinct-aux-f!!2 #855
[mk-app] #2116 unique-value!66
[attach-enode] #2116 0
[mk-app] #2117 = #2115 #2116
[attach-enode] #855 0
[attach-enode] #2115 0
[attach-enode] #2117 0
[assign] #2117 justification -1: 
[mk-app] #2118 distinct-aux-f!!2 #856
[mk-app] #2119 unique-value!67
[attach-enode] #2119 0
[mk-app] #2120 = #2118 #2119
[attach-enode] #856 0
[attach-enode] #2118 0
[attach-enode] #2120 0
[assign] #2120 justification -1: 
[mk-app] #2121 distinct-aux-f!!2 #857
[mk-app] #2122 unique-value!68
[attach-enode] #2122 0
[mk-app] #2123 = #2121 #2122
[attach-enode] #857 0
[attach-enode] #2121 0
[attach-enode] #2123 0
[assign] #2123 justification -1: 
[mk-app] #2124 distinct-aux-f!!2 #858
[mk-app] #2125 unique-value!69
[attach-enode] #2125 0
[mk-app] #2126 = #2124 #2125
[attach-enode] #858 0
[attach-enode] #2124 0
[attach-enode] #2126 0
[assign] #2126 justification -1: 
[mk-app] #2127 distinct-aux-f!!2 #859
[mk-app] #2128 unique-value!70
[attach-enode] #2128 0
[mk-app] #2129 = #2127 #2128
[attach-enode] #859 0
[attach-enode] #2127 0
[attach-enode] #2129 0
[assign] #2129 justification -1: 
[mk-app] #2130 distinct-aux-f!!2 #860
[mk-app] #2131 unique-value!71
[attach-enode] #2131 0
[mk-app] #2132 = #2130 #2131
[attach-enode] #860 0
[attach-enode] #2130 0
[attach-enode] #2132 0
[assign] #2132 justification -1: 
[mk-app] #2133 distinct-aux-f!!2 #861
[mk-app] #2134 unique-value!72
[attach-enode] #2134 0
[mk-app] #2135 = #2133 #2134
[attach-enode] #861 0
[attach-enode] #2133 0
[attach-enode] #2135 0
[assign] #2135 justification -1: 
[mk-app] #2136 distinct-aux-f!!2 #862
[mk-app] #2137 unique-value!73
[attach-enode] #2137 0
[mk-app] #2138 = #2136 #2137
[attach-enode] #862 0
[attach-enode] #2136 0
[attach-enode] #2138 0
[assign] #2138 justification -1: 
[mk-app] #2139 distinct-aux-f!!2 #863
[mk-app] #2140 unique-value!74
[attach-enode] #2140 0
[mk-app] #2141 = #2139 #2140
[attach-enode] #863 0
[attach-enode] #2139 0
[attach-enode] #2141 0
[assign] #2141 justification -1: 
[mk-app] #2142 distinct-aux-f!!2 #864
[mk-app] #2143 unique-value!75
[attach-enode] #2143 0
[mk-app] #2144 = #2142 #2143
[attach-enode] #864 0
[attach-enode] #2142 0
[attach-enode] #2144 0
[assign] #2144 justification -1: 
[mk-app] #2145 distinct-aux-f!!2 #865
[mk-app] #2146 unique-value!76
[attach-enode] #2146 0
[mk-app] #2147 = #2145 #2146
[attach-enode] #865 0
[attach-enode] #2145 0
[attach-enode] #2147 0
[assign] #2147 justification -1: 
[mk-app] #2148 distinct-aux-f!!2 #866
[mk-app] #2149 unique-value!77
[attach-enode] #2149 0
[mk-app] #2150 = #2148 #2149
[attach-enode] #866 0
[attach-enode] #2148 0
[attach-enode] #2150 0
[assign] #2150 justification -1: 
[mk-app] #2151 distinct-aux-f!!2 #867
[mk-app] #2152 unique-value!78
[attach-enode] #2152 0
[mk-app] #2153 = #2151 #2152
[attach-enode] #867 0
[attach-enode] #2151 0
[attach-enode] #2153 0
[assign] #2153 justification -1: 
[mk-app] #2154 distinct-aux-f!!2 #868
[mk-app] #2155 unique-value!79
[attach-enode] #2155 0
[mk-app] #2156 = #2154 #2155
[attach-enode] #868 0
[attach-enode] #2154 0
[attach-enode] #2156 0
[assign] #2156 justification -1: 
[mk-app] #2157 distinct-aux-f!!2 #869
[mk-app] #2158 unique-value!80
[attach-enode] #2158 0
[mk-app] #2159 = #2157 #2158
[attach-enode] #869 0
[attach-enode] #2157 0
[attach-enode] #2159 0
[assign] #2159 justification -1: 
[mk-app] #2160 distinct-aux-f!!2 #870
[mk-app] #2161 unique-value!81
[attach-enode] #2161 0
[mk-app] #2162 = #2160 #2161
[attach-enode] #870 0
[attach-enode] #2160 0
[attach-enode] #2162 0
[assign] #2162 justification -1: 
[mk-app] #2163 distinct-aux-f!!2 #871
[mk-app] #2164 unique-value!82
[attach-enode] #2164 0
[mk-app] #2165 = #2163 #2164
[attach-enode] #871 0
[attach-enode] #2163 0
[attach-enode] #2165 0
[assign] #2165 justification -1: 
[attach-enode] #873 0
[attach-enode] #874 0
[attach-enode] #875 0
[attach-enode] #880 0
[attach-enode] #881 0
[attach-enode] #882 0
[attach-enode] #883 0
[attach-enode] #884 0
[attach-enode] #885 0
[attach-enode] #886 0
[attach-enode] #887 0
[attach-enode] #888 0
[attach-enode] #889 0
[attach-enode] #890 0
[attach-enode] #891 0
[attach-enode] #892 0
[attach-enode] #893 0
[attach-enode] #894 0
[attach-enode] #895 0
[attach-enode] #896 0
[attach-enode] #897 0
[attach-enode] #898 0
[attach-enode] #899 0
[attach-enode] #900 0
[attach-enode] #901 0
[attach-enode] #902 0
[attach-enode] #903 0
[attach-enode] #904 0
[attach-enode] #905 0
[attach-enode] #910 0
[attach-enode] #911 0
[attach-enode] #915 0
[attach-enode] #916 0
[attach-enode] #920 0
[assign] #920 justification -1: 
[attach-enode] #921 0
[assign] #921 justification -1: 
[assign] #915 justification -1: 
[attach-enode] #922 0
[assign] #922 justification -1: 
[attach-enode] #923 0
[assign] #923 justification -1: 
[attach-enode] #924 0
[assign] #924 justification -1: 
[attach-enode] #925 0
[assign] #925 justification -1: 
[attach-enode] #926 0
[assign] #926 justification -1: 
[attach-enode] #927 0
[assign] #927 justification -1: 
[assign] #873 justification -1: 
[assign] #880 justification -1: 
[attach-enode] #928 0
[assign] #928 justification -1: 
[attach-enode] #929 0
[assign] #929 justification -1: 
[attach-enode] #930 0
[assign] #930 justification -1: 
[attach-enode] #931 0
[assign] #931 justification -1: 
[attach-enode] #932 0
[assign] #932 justification -1: 
[assign] #910 justification -1: 
[attach-enode] #933 0
[assign] #933 justification -1: 
[attach-enode] #934 0
[assign] #934 justification -1: 
[attach-enode] #935 0
[assign] #935 justification -1: 
[attach-enode] #936 0
[assign] #936 justification -1: 
[attach-enode] #937 0
[assign] #937 justification -1: 
[attach-enode] #938 0
[assign] #938 justification -1: 
[attach-enode] #939 0
[assign] #939 justification -1: 
[attach-enode] #940 0
[assign] #940 justification -1: 
[attach-enode] #941 0
[assign] #941 justification -1: 
[attach-enode] #942 0
[assign] #942 justification -1: 
[assign] #952 justification -1: 
[assign] #963 justification -1: 
[assign] #1953 justification -1: 
[assign] #980 justification -1: 
[assign] #987 justification -1: 
[assign] #992 justification -1: 
[assign] #999 justification -1: 
[assign] #1005 justification -1: 
[assign] #1016 justification -1: 
[assign] #1019 justification -1: 
[assign] #1958 justification -1: 
[assign] #1962 justification -1: 
[assign] #1966 justification -1: 
[assign] #1973 justification -1: 
[assign] #1975 justification -1: 
[assign] #1978 justification -1: 
[assign] #1980 justification -1: 
[assign] #1985 justification -1: 
[assign] #1987 justification -1: 
[assign] #1989 justification -1: 
[attach-enode] #1123 0
[attach-enode] #1148 0
[attach-enode] #1006 0
[attach-enode] #1183 0
[assign] #1183 justification -1: 
[attach-enode] #1184 0
[assign] #1184 justification -1: 
[assign] #1191 justification -1: 
[assign] #1209 justification -1: 
[attach-enode] #1210 0
[attach-enode] #1224 0
[assign] #1224 justification -1: 
[attach-enode] #1225 0
[attach-enode] #1235 0
[assign] #1235 justification -1: 
[attach-enode] #1236 0
[attach-enode] #1254 0
[assign] #1254 justification -1: 
[attach-enode] #1255 0
[attach-enode] #1267 0
[assign] #1267 justification -1: 
[assign] #1272 justification -1: 
[assign] #2020 justification -1: 
[attach-enode] #1287 0
[assign] #2025 justification -1: 
[assign] #2027 justification -1: 
[attach-enode] #1315 0
[assign] #1315 justification -1: 
[attach-enode] #1316 0
[attach-enode] #1330 0
[assign] #1330 justification -1: 
[assign] #1335 justification -1: 
[assign] #1351 justification -1: 
[attach-enode] #1352 0
[assign] #1371 justification -1: 
[assign] #1377 justification -1: 
[attach-enode] #1378 0
[assign] #1378 justification -1: 
[attach-enode] #1379 0
[attach-enode] #1380 0
[attach-enode] #1381 0
[attach-enode] #1382 0
[attach-enode] #1386 0
[assign] #1386 justification -1: 
[attach-enode] #1387 0
[assign] #1387 justification -1: 
[attach-enode] #1388 0
[attach-enode] #1396 0
[assign] #1396 justification -1: 
[attach-enode] #1397 0
[attach-enode] #1418 0
[assign] #1418 justification -1: 
[attach-enode] #1419 0
[attach-enode] #1434 0
[assign] #1434 justification -1: 
[attach-enode] #1435 0
[attach-enode] #1470 0
[assign] #1470 justification -1: 
[attach-enode] #1471 0
[attach-enode] #1479 0
[assign] #1479 justification -1: 
[attach-enode] #1480 0
[attach-enode] #1488 0
[assign] #1488 justification -1: 
[attach-enode] #1489 0
[attach-enode] #1502 0
[assign] #1502 justification -1: 
[attach-enode] #1503 0
[attach-enode] #1517 0
[assign] #1517 justification -1: 
[attach-enode] #1518 0
[attach-enode] #1526 0
[assign] #1526 justification -1: 
[attach-enode] #1532 0
[attach-enode] #1545 0
[assign] #1545 justification -1: 
[attach-enode] #1546 0
[attach-enode] #1560 0
[assign] #1560 justification -1: 
[attach-enode] #1561 0
[attach-enode] #1573 0
[assign] #1573 justification -1: 
[attach-enode] #1574 0
[assign] #1588 justification -1: 
[attach-enode] #1589 0
[assign] #1589 justification -1: 
[attach-enode] #1590 0
[attach-enode] #1614 0
[assign] #1614 justification -1: 
[attach-enode] #1615 0
[attach-enode] #1642 0
[assign] #1642 justification -1: 
[attach-enode] #1643 0
[assign] #2045 justification -1: 
[assign] #2047 justification -1: 
[assign] #2049 justification -1: 
[assign] #2051 justification -1: 
[assign] #2053 justification -1: 
[assign] #2056 justification -1: 
[assign] #2058 justification -1: 
[assign] #1723 justification -1: 
[assign] #1729 justification -1: 
[assign] #2061 justification -1: 
[assign] #2063 justification -1: 
[assign] #2065 justification -1: 
[assign] #1763 justification -1: 
[assign] #1774 justification -1: 
[assign] #1785 justification -1: 
[assign] #1794 justification -1: 
[assign] #916 bin 211
[assign] #875 bin 180
[assign] #874 bin 180
[assign] #905 bin 183
[assign] #904 bin 183
[assign] #903 bin 183
[assign] #902 bin 183
[assign] #901 bin 183
[assign] #900 bin 183
[assign] #899 bin 183
[assign] #898 bin 183
[assign] #897 bin 183
[assign] #896 bin 183
[assign] #895 bin 183
[assign] #894 bin 183
[assign] #893 bin 183
[assign] #892 bin 183
[assign] #891 bin 183
[assign] #890 bin 183
[assign] #889 bin 183
[assign] #888 bin 183
[assign] #887 bin 183
[assign] #886 bin 183
[assign] #885 bin 183
[assign] #884 bin 183
[assign] #883 bin 183
[assign] #882 bin 183
[assign] #881 bin 183
[assign] #911 bin 209
[attach-enode] #136 0
[attach-enode] #141 0
[attach-enode] #185 0
[attach-enode] #196 0
[attach-enode] #204 0
[attach-enode] #212 0
[attach-enode] #245 0
[attach-enode] #953 0
[eq-expl] #273 root
[eq-expl] #1380 root
[new-match] 0x560962123300 #1862 #451 #1380 #273 ; #1386
[mk-app] #2166 * #366 #315
[mk-app] #2167 + #1380 #2166
[mk-app] #2168 >= #2167 #337
[mk-app] #2169 not #2168
[mk-app] #2170 * #366 #333
[mk-app] #2171 + #1380 #2170
[mk-app] #2172 >= #2171 #337
[mk-app] #2173 or #2169 #2172
[mk-app] #2174 = #2173 #1386
[mk-app] #2175 not #2174
[mk-app] #2176 + #2166 #1380
[inst-discovered] theory-solving 0 arith# ; #2167
[mk-app] #2177 = #2167 #2176
[instance] 0 #2177
[attach-enode] #2177 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2177 * #366 #1380
[mk-app] #2178 + #315 #2177
[mk-app] #2179 <= #2178 #337
[mk-app] #2180 >= #2176 #337
[inst-discovered] theory-solving 0 arith# ; #2180
[mk-app] #2181 = #2180 #2179
[instance] 0 #2181
[attach-enode] #2181 0
[end-of-instance]
[mk-app] #2176 not #2179
[mk-app] #2180 + #2170 #1380
[inst-discovered] theory-solving 0 arith# ; #2171
[mk-app] #2181 = #2171 #2180
[instance] 0 #2181
[attach-enode] #2181 0
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2181 + #333 #2177
[mk-app] #2182 <= #2181 #337
[mk-app] #2183 >= #2180 #337
[inst-discovered] theory-solving 0 arith# ; #2183
[mk-app] #2184 = #2183 #2182
[instance] 0 #2184
[attach-enode] #2184 0
[end-of-instance]
[mk-app] #2180 or #2176 #2182
[mk-app] #2183 = #2180 #1386
[mk-app] #2184 not #2180
[mk-app] #2185 not #2183
[inst-discovered] theory-solving 0 basic# ; #2185
[mk-app] #2184 = #2185 #2185
[instance] 0 #2184
[attach-enode] #2184 0
[end-of-instance]
[mk-app] #2184 not #1862
[mk-app] #2186 or #2184 #2185
[instance] 0x560962123300 ; 1
[attach-enode] #366 1
[attach-enode] #2177 1
[attach-enode] #2178 1
[attach-enode] #2181 1
[assign] (not #2183) justification -1: 60
[end-of-instance]
[assign] (not #2180) bin -364
[assign] (not #2182) bin -363
[assign] #2179 bin -363
[mk-app] #2187 <= #315 #319
[mk-app] #2188 >= #315 #319
[assign] #2187 justification -1: 48
[assign] #2188 justification -1: 48
[mk-app] #2189 <= #333 #316
[mk-app] #2190 >= #333 #316
[assign] #2189 justification -1: 53
[assign] #2190 justification -1: 53
[push] 0
[mk-app] #2191 a!
[mk-app] #2192 <= #337 #2191
[attach-meaning] #366 arith (- 1)
[mk-app] #2193 * #366 #2191
[mk-app] #2194 >= #2191 #337
[inst-discovered] theory-solving 0 arith# ; #2192
[mk-app] #2193 = #2192 #2194
[instance] 0 #2193
[attach-enode] #2193 0
[end-of-instance]
[mk-app] #2193 b!
[mk-app] #2195 <= #337 #2193
[attach-meaning] #366 arith (- 1)
[mk-app] #2196 * #366 #2193
[mk-app] #2197 >= #2193 #337
[inst-discovered] theory-solving 0 arith# ; #2195
[mk-app] #2196 = #2195 #2197
[instance] 0 #2196
[attach-enode] #2196 0
[end-of-instance]
[mk-app] #2196 decrease%init0
[mk-app] #2198 = #2196 #2193
[mk-app] #2199 = #2193 #337
[mk-app] #2200 %%switch_label%%0
[mk-app] #2201 => #2199 #2200
[mk-app] #2202 not #2199
[mk-app] #2203 tmp%1
[mk-app] #2204 Sub #2193 #292
[mk-app] #2205 nClip #2204
[mk-app] #2206 = #2203 #2205
[mk-app] #2207 %%location_label%%0
[mk-app] #2208 I #2203
[mk-app] #2209 I #2196
[mk-app] #2210 check_decrease_height #2208 #2209 #2
[mk-app] #2211 => #2207 #2210
[mk-app] #2212 ens%the_q!model.lemma_pow2_add. #2191 #2203
[mk-app] #2213 tmp%2
[mk-app] #2214 Add #2191 #2193
[mk-app] #2215 nClip #2214
[mk-app] #2216 I #2215
[mk-app] #2217 the_q!model.pow2.? #2216
[mk-app] #2218 Sub #2215 #292
[mk-app] #2219 nClip #2218
[mk-app] #2220 I #2219
[mk-app] #2221 the_q!model.pow2.? #2220
[mk-app] #2222 Mul #1196 #2221
[mk-app] #2223 = #2217 #2222
[mk-app] #2224 = #2213 #2223
[mk-app] #2225 %%location_label%%1
[mk-app] #2226 => #2225 #2213
[mk-app] #2227 tmp%3
[mk-app] #2228 I #2193
[mk-app] #2229 the_q!model.pow2.? #2228
[mk-app] #2230 I #2205
[mk-app] #2231 the_q!model.pow2.? #2230
[mk-app] #2232 Mul #1196 #2231
[mk-app] #2233 = #2229 #2232
[mk-app] #2234 = #2227 #2233
[mk-app] #2235 %%location_label%%2
[mk-app] #2236 => #2235 #2227
[mk-app] #2237 %%location_label%%3
[mk-app] #2238 => #2237 #1
[mk-app] #2239 I #2191
[mk-app] #2240 the_q!model.pow2.? #2239
[mk-app] #2241 Mul #2240 #2231
[mk-app] #2242 Mul #1196 #2241
[mk-app] #2243 Mul #2240 #2232
[mk-app] #2244 = #2242 #2243
[mk-app] #2245 => #2244 #2200
[mk-app] #2246 and #2238 #2245
[mk-app] #2247 => #2227 #2246
[mk-app] #2248 and #2236 #2247
[mk-app] #2249 => #2234 #2248
[mk-app] #2250 => #2213 #2249
[mk-app] #2251 and #2226 #2250
[mk-app] #2252 => #2224 #2251
[mk-app] #2253 => #2212 #2252
[mk-app] #2254 and #2211 #2253
[mk-app] #2255 => #2206 #2254
[mk-app] #2256 => #2202 #2255
[mk-app] #2257 and #2201 #2256
[mk-app] #2258 not #2200
[mk-app] #2259 %%location_label%%4
[mk-app] #2260 Mul #2240 #2229
[mk-app] #2261 = #2217 #2260
[mk-app] #2262 => #2259 #2261
[mk-app] #2263 and #2258 #2262
[mk-app] #2264 or #2257 #2263
[mk-app] #2265 => #2198 #2264
[mk-app] #2266 not #2265
[mk-app] #2267 or #2202 #2200
[inst-discovered] theory-solving 0 basic# ; #2201
[mk-app] #2268 = #2201 #2267
[instance] 0 #2268
[attach-enode] #2268 0
[end-of-instance]
[mk-app] #2268 not #2207
[mk-app] #2269 or #2268 #2210
[inst-discovered] theory-solving 0 basic# ; #2211
[mk-app] #2270 = #2211 #2269
[instance] 0 #2270
[attach-enode] #2270 0
[end-of-instance]
[mk-app] #2270 not #2225
[mk-app] #2271 or #2270 #2213
[inst-discovered] theory-solving 0 basic# ; #2226
[mk-app] #2272 = #2226 #2271
[instance] 0 #2272
[attach-enode] #2272 0
[end-of-instance]
[mk-app] #2272 not #2235
[mk-app] #2273 or #2272 #2227
[inst-discovered] theory-solving 0 basic# ; #2236
[mk-app] #2274 = #2236 #2273
[instance] 0 #2274
[attach-enode] #2274 0
[end-of-instance]
[mk-app] #2274 not #2237
[inst-discovered] theory-solving 0 basic# ; #2238
[mk-app] #2274 = #2238 #1
[instance] 0 #2274
[attach-enode] #2274 0
[end-of-instance]
[mk-app] #2274 not #2244
[mk-app] #2275 or #2274 #2200
[inst-discovered] theory-solving 0 basic# ; #2245
[mk-app] #2276 = #2245 #2275
[instance] 0 #2276
[attach-enode] #2276 0
[end-of-instance]
[mk-app] #2276 and #1 #2275
[inst-discovered] theory-solving 0 basic# ; #2276
[mk-app] #2277 = #2276 #2275
[instance] 0 #2277
[attach-enode] #2277 0
[end-of-instance]
[mk-app] #2276 not #2227
[mk-app] #2277 or #2276 #2274 #2200
[mk-app] #2278 => #2227 #2275
[inst-discovered] theory-solving 0 basic# ; #2278
[mk-app] #2279 = #2278 #2277
[instance] 0 #2279
[attach-enode] #2279 0
[end-of-instance]
[mk-app] #2275 and #2273 #2277
[mk-app] #2278 not #2234
[mk-app] #2279 or #2278 #2275
[mk-app] #2280 => #2234 #2275
[inst-discovered] theory-solving 0 basic# ; #2280
[mk-app] #2281 = #2280 #2279
[instance] 0 #2281
[attach-enode] #2281 0
[end-of-instance]
[mk-app] #2280 not #2213
[mk-app] #2281 or #2280 #2278 #2275
[mk-app] #2282 => #2213 #2279
[inst-discovered] theory-solving 0 basic# ; #2282
[mk-app] #2283 = #2282 #2281
[instance] 0 #2283
[attach-enode] #2283 0
[end-of-instance]
[mk-app] #2279 and #2271 #2281
[mk-app] #2282 not #2224
[mk-app] #2283 or #2282 #2279
[mk-app] #2284 => #2224 #2279
[inst-discovered] theory-solving 0 basic# ; #2284
[mk-app] #2285 = #2284 #2283
[instance] 0 #2285
[attach-enode] #2285 0
[end-of-instance]
[mk-app] #2284 not #2212
[mk-app] #2285 or #2284 #2282 #2279
[mk-app] #2286 => #2212 #2283
[inst-discovered] theory-solving 0 basic# ; #2286
[mk-app] #2287 = #2286 #2285
[instance] 0 #2287
[attach-enode] #2287 0
[end-of-instance]
[mk-app] #2283 and #2269 #2285
[mk-app] #2286 not #2206
[mk-app] #2287 or #2286 #2283
[mk-app] #2288 => #2206 #2283
[inst-discovered] theory-solving 0 basic# ; #2288
[mk-app] #2289 = #2288 #2287
[instance] 0 #2289
[attach-enode] #2289 0
[end-of-instance]
[mk-app] #2288 or #2199 #2286 #2283
[mk-app] #2289 => #2202 #2287
[inst-discovered] theory-solving 0 basic# ; #2289
[mk-app] #2290 = #2289 #2288
[instance] 0 #2290
[attach-enode] #2290 0
[end-of-instance]
[mk-app] #2287 and #2267 #2288
[mk-app] #2289 not #2259
[mk-app] #2290 or #2289 #2261
[inst-discovered] theory-solving 0 basic# ; #2262
[mk-app] #2291 = #2262 #2290
[instance] 0 #2291
[attach-enode] #2291 0
[end-of-instance]
[mk-app] #2291 and #2258 #2290
[mk-app] #2292 or #2287 #2291
[inst-discovered] theory-solving 0 basic# ; #2292
[mk-app] #2293 = #2292 #2292
[instance] 0 #2293
[attach-enode] #2293 0
[end-of-instance]
[mk-app] #2293 not #2198
[mk-app] #2294 or #2293 #2287 #2291
[mk-app] #2295 => #2198 #2292
[inst-discovered] theory-solving 0 basic# ; #2295
[mk-app] #2296 = #2295 #2294
[instance] 0 #2296
[attach-enode] #2296 0
[end-of-instance]
[mk-app] #2292 not #2294
[mk-app] #2295 not #2287
[mk-app] #2296 not #2291
[begin-check] 1
[inst-discovered] theory-solving 0 basic# ; #2267
[mk-app] #2293 = #2267 #2267
[instance] 0 #2293
[attach-enode] #2293 0
[end-of-instance]
[mk-app] #2293 check_decrease_height #2208 #2228 #2
[mk-app] #2294 or #2268 #2293
[inst-discovered] theory-solving 0 basic# ; #2282
[mk-app] #2292 = #2282 #2282
[instance] 0 #2292
[attach-enode] #2292 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2271
[mk-app] #2292 = #2271 #2271
[instance] 0 #2292
[attach-enode] #2292 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2278
[mk-app] #2292 = #2278 #2278
[instance] 0 #2292
[attach-enode] #2292 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2273
[mk-app] #2292 = #2273 #2273
[instance] 0 #2292
[attach-enode] #2292 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2277
[mk-app] #2292 = #2277 #2277
[instance] 0 #2292
[attach-enode] #2292 0
[end-of-instance]
[mk-app] #2292 and #2294 #2285
[mk-app] #2297 or #2199 #2286 #2292
[inst-discovered] theory-solving 0 basic# ; #2297
[mk-app] #2298 = #2297 #2297
[instance] 0 #2298
[attach-enode] #2298 0
[end-of-instance]
[mk-app] #2298 and #2267 #2297
[mk-app] #2299 not #2298
[inst-discovered] theory-solving 0 basic# ; #2267
[mk-app] #2269 = #2267 #2267
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2282
[mk-app] #2269 = #2282 #2282
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2271
[mk-app] #2269 = #2271 #2271
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2278
[mk-app] #2269 = #2278 #2278
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2273
[mk-app] #2269 = #2273 #2273
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2277
[mk-app] #2269 = #2277 #2277
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2297
[mk-app] #2269 = #2297 #2297
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2267
[mk-app] #2269 = #2267 #2267
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2282
[mk-app] #2269 = #2282 #2282
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2271
[mk-app] #2269 = #2271 #2271
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2278
[mk-app] #2269 = #2278 #2278
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2273
[mk-app] #2269 = #2273 #2273
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2277
[mk-app] #2269 = #2277 #2277
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2297
[mk-app] #2269 = #2297 #2297
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2267
[mk-app] #2269 = #2267 #2267
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2282
[mk-app] #2269 = #2282 #2282
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2271
[mk-app] #2269 = #2271 #2271
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2278
[mk-app] #2269 = #2278 #2278
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2273
[mk-app] #2269 = #2273 #2273
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2277
[mk-app] #2269 = #2277 #2277
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2297
[mk-app] #2269 = #2297 #2297
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2267
[mk-app] #2269 = #2267 #2267
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2282
[mk-app] #2269 = #2282 #2282
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2271
[mk-app] #2269 = #2271 #2271
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2278
[mk-app] #2269 = #2278 #2278
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2273
[mk-app] #2269 = #2273 #2273
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2277
[mk-app] #2269 = #2277 #2277
[instance] 0 #2269
[attach-enode] #2269 0
[end-of-instance]
[mk-app] #2269 not #2273
[mk-app] #2283 not #2277
[mk-app] #2288 or #2269 #2283
[mk-app] #2287 not #2288
[inst-discovered] theory-solving 0 basic# ; #2275
[mk-app] #2295 = #2275 #2287
[instance] 0 #2295
[attach-enode] #2295 0
[end-of-instance]
[mk-app] #2295 or #2280 #2278 #2287
[mk-app] #2300 not #2271
[mk-app] #2301 not #2295
[mk-app] #2302 or #2300 #2301
[mk-app] #2303 not #2302
[mk-app] #2304 and #2271 #2295
[inst-discovered] theory-solving 0 basic# ; #2304
[mk-app] #2305 = #2304 #2303
[instance] 0 #2305
[attach-enode] #2305 0
[end-of-instance]
[mk-app] #2304 or #2284 #2282 #2303
[mk-app] #2305 not #2294
[mk-app] #2306 not #2304
[mk-app] #2307 or #2305 #2306
[mk-app] #2308 not #2307
[mk-app] #2309 and #2294 #2304
[inst-discovered] theory-solving 0 basic# ; #2309
[mk-app] #2310 = #2309 #2308
[instance] 0 #2310
[attach-enode] #2310 0
[end-of-instance]
[mk-app] #2309 or #2199 #2286 #2308
[inst-discovered] theory-solving 0 basic# ; #2309
[mk-app] #2310 = #2309 #2309
[instance] 0 #2310
[attach-enode] #2310 0
[end-of-instance]
[mk-app] #2310 not #2267
[mk-app] #2311 not #2309
[mk-app] #2312 or #2310 #2311
[mk-app] #2313 not #2312
[mk-app] #2314 and #2267 #2309
[inst-discovered] theory-solving 0 basic# ; #2314
[mk-app] #2315 = #2314 #2313
[instance] 0 #2315
[attach-enode] #2315 0
[end-of-instance]
[mk-app] #2314 not #2313
[inst-discovered] theory-solving 0 basic# ; #2314
[mk-app] #2315 = #2314 #2312
[instance] 0 #2315
[attach-enode] #2315 0
[end-of-instance]
[mk-app] #2313 not #2290
[mk-app] #2314 or #2200 #2313
[mk-app] #2315 not #2314
[inst-discovered] theory-solving 0 basic# ; #2291
[mk-app] #2316 = #2291 #2315
[instance] 0 #2316
[attach-enode] #2316 0
[end-of-instance]
[mk-app] #2316 not #2315
[inst-discovered] theory-solving 0 basic# ; #2316
[mk-app] #2317 = #2316 #2314
[instance] 0 #2317
[attach-enode] #2317 0
[end-of-instance]
[mk-app] #2291 or #2276 #2274
[mk-app] #2296 or #2291 #2200
[mk-app] #2275 not #2296
[mk-app] #2281 or #2269 #2275
[mk-app] #2279 not #2281
[mk-app] #2285 or #2280 #2278
[mk-app] #2292 or #2285 #2279
[mk-app] #2297 not #2292
[mk-app] #2298 or #2300 #2297
[mk-app] #2299 not #2298
[mk-app] #2315 or #2284 #2282
[mk-app] #2316 or #2315 #2299
[mk-app] #2317 not #2316
[mk-app] #2318 or #2305 #2317
[mk-app] #2319 not #2318
[mk-app] #2320 or #2199 #2286
[mk-app] #2321 or #2320 #2319
[mk-app] #2322 not #2321
[mk-app] #2323 or #2310 #2322
[inst-discovered] theory-solving 0 basic# ; #2267
[mk-app] #2277 = #2267 #2267
[instance] 0 #2277
[attach-enode] #2277 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2320
[mk-app] #2277 = #2320 #2320
[instance] 0 #2277
[attach-enode] #2277 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2282
[mk-app] #2277 = #2282 #2282
[instance] 0 #2277
[attach-enode] #2277 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2271
[mk-app] #2277 = #2271 #2271
[instance] 0 #2277
[attach-enode] #2277 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2278
[mk-app] #2277 = #2278 #2278
[instance] 0 #2277
[attach-enode] #2277 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2273
[mk-app] #2277 = #2273 #2273
[instance] 0 #2277
[attach-enode] #2277 0
[end-of-instance]
[mk-app] #2277 or #2276 #2274 #2200
[inst-discovered] theory-solving 0 basic# ; #2296
[mk-app] #2283 = #2296 #2277
[instance] 0 #2283
[attach-enode] #2283 0
[end-of-instance]
[mk-app] #2283 not #2277
[mk-app] #2288 or #2269 #2283
[mk-app] #2287 not #2288
[mk-app] #2295 or #2280 #2278 #2287
[mk-app] #2301 or #2285 #2287
[inst-discovered] theory-solving 0 basic# ; #2301
[mk-app] #2302 = #2301 #2295
[instance] 0 #2302
[attach-enode] #2302 0
[end-of-instance]
[mk-app] #2301 not #2295
[mk-app] #2302 or #2300 #2301
[mk-app] #2303 not #2302
[mk-app] #2304 or #2284 #2282 #2303
[mk-app] #2306 or #2315 #2303
[inst-discovered] theory-solving 0 basic# ; #2306
[mk-app] #2307 = #2306 #2304
[instance] 0 #2307
[attach-enode] #2307 0
[end-of-instance]
[mk-app] #2306 not #2304
[mk-app] #2307 or #2305 #2306
[mk-app] #2308 not #2307
[mk-app] #2309 or #2199 #2286 #2308
[mk-app] #2311 or #2320 #2308
[inst-discovered] theory-solving 0 basic# ; #2311
[mk-app] #2312 = #2311 #2309
[instance] 0 #2312
[attach-enode] #2312 0
[end-of-instance]
[mk-app] #2311 not #2309
[mk-app] #2312 or #2310 #2311
[inst-discovered] theory-solving 0 basic# ; #2267
[mk-app] #2321 = #2267 #2267
[instance] 0 #2321
[attach-enode] #2321 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2271
[mk-app] #2321 = #2271 #2271
[instance] 0 #2321
[attach-enode] #2321 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2273
[mk-app] #2321 = #2273 #2273
[instance] 0 #2321
[attach-enode] #2321 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2277
[mk-app] #2321 = #2277 #2277
[instance] 0 #2321
[attach-enode] #2321 0
[end-of-instance]
[inst-discovered] theory-solving 0 basic# ; #2309
[mk-app] #2321 = #2309 #2309
[instance] 0 #2321
[attach-enode] #2321 0
[end-of-instance]
[mk-app] #2321 or #2310 #2202
[mk-app] #2322 or #2310 #2206
[mk-app] #2323 or #2310 #2307
[mk-app] #2324 or #2200 #2259
[mk-app] #2325 not #2261
[mk-app] #2326 or #2200 #2325
[mk-app] #2289 or #2202 #2199
[mk-app] #2290 or #2202 #2258
[mk-app] #2313 or #2206 #2199
[mk-app] #2314 or #2206 #2258
[mk-app] #2309 or #2307 #2199
[mk-app] #2311 or #2307 #2258
[assign] #23 justification -1: 
[attach-enode] #2191 0
[assign] #2194 justification -1: 
[attach-enode] #2193 0
[assign] #2197 justification -1: 
[attach-enode] #2196 0
[attach-enode] #2198 0
[assign] #2198 justification -1: 
[attach-enode] #337 0
[attach-enode] #2199 0
[mk-app] #2308 <= #2193 #337
[attach-enode] #2203 0
[attach-enode] #292 0
[attach-enode] #2204 0
[attach-enode] #2205 0
[attach-enode] #2206 0
[attach-enode] #2208 0
[attach-enode] #2228 0
[attach-enode] #2293 0
[attach-enode] #2212 0
[attach-enode] #2214 0
[attach-enode] #2215 0
[attach-enode] #2216 0
[attach-enode] #2217 0
[attach-enode] #1196 0
[attach-enode] #2218 0
[attach-enode] #2219 0
[attach-enode] #2220 0
[attach-enode] #2221 0
[attach-enode] #2222 0
[attach-enode] #2223 0
[attach-enode] #2229 0
[attach-enode] #2230 0
[attach-enode] #2231 0
[attach-enode] #2232 0
[attach-enode] #2233 0
[attach-enode] #2239 0
[attach-enode] #2240 0
[attach-enode] #2241 0
[attach-enode] #2242 0
[attach-enode] #2243 0
[attach-enode] #2244 0
[attach-enode] #2260 0
[attach-enode] #2261 0
[assign] #29 bin 1
[decide-and-or] #275 #272
[push] 1
[assign] #272 decision axiom
[decide-and-or] #1990 #1146
[push] 2
[assign] (not #1123) decision axiom
[eq-expl] #792 root
[new-match] 0x56096213b7d8 #29 #28 #792 ; #1123
[mk-app] #2173 = #1123 #874
[mk-app] #2174 not #29
[mk-app] #2175 or #2174 #2173
[instance] 0x56096213b7d8 ; 1
[assign] (not #2173) justification -1: 181 -256
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2173
[conflict] #2173
[pop] 1 3
[assign] #2173 axiom
[assign] #1123 clause 256 -399
[assign] #1994 bin 256
[decide-and-or] #1998 #1181
[push] 2
[assign] (not #1148) decision axiom
[eq-expl] #793 root
[new-match] 0x56096213b838 #29 #28 #793 ; #1148
[mk-app] #2174 = #1148 #875
[mk-app] #2175 not #29
[mk-app] #2267 or #2175 #2174
[instance] 0x56096213b838 ; 1
[assign] (not #2174) justification -1: 182 -258
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2174
[conflict] #2174
[pop] 1 3
[assign] #2174 axiom
[assign] #1148 clause 258 -400
[assign] #2005 bin 258
[decide-and-or] #1223 #1222
[push] 2
[assign] (not #1210) decision axiom
[eq-expl] #794 root
[new-match] 0x56096213b898 #29 #28 #794 ; #1210
[mk-app] #2175 = #1210 #1184
[mk-app] #2267 not #29
[mk-app] #2310 or #2267 #2175
[instance] 0x56096213b898 ; 1
[assign] (not #2175) justification -1: 261 -264
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2175
[conflict] #2175
[pop] 1 3
[assign] #2175 axiom
[assign] #1210 clause 264 -401
[assign] #1221 bin 264
[decide-and-or] #1234 #1233
[push] 2
[assign] (not #1225) decision axiom
[eq-expl] #795 root
[new-match] 0x56096213b8f8 #29 #28 #795 ; #1225
[mk-app] #2267 = #1225 #1224
[mk-app] #2310 not #29
[mk-app] #2323 or #2310 #2267
[instance] 0x56096213b8f8 ; 1
[assign] (not #2267) justification -1: 266 -267
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2267
[conflict] #2267
[pop] 1 3
[assign] #2267 axiom
[assign] #1225 clause 267 -402
[assign] #1231 bin 267
[decide-and-or] #1253 #1252
[push] 2
[assign] (not #1236) decision axiom
[eq-expl] #796 root
[new-match] 0x56096213b958 #29 #28 #796 ; #1236
[mk-app] #2310 = #1236 #1235
[mk-app] #2323 not #29
[mk-app] #2322 or #2323 #2310
[instance] 0x56096213b958 ; 1
[assign] (not #2310) justification -1: 269 -270
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2310
[conflict] #2310
[pop] 1 3
[assign] #2310 axiom
[assign] #1236 clause 270 -403
[assign] #1251 bin 270
[decide-and-or] #2015 #1265
[push] 2
[assign] (not #1255) decision axiom
[eq-expl] #797 root
[new-match] 0x56096213b9b8 #29 #28 #797 ; #1255
[mk-app] #2323 = #1255 #1254
[mk-app] #2322 not #29
[mk-app] #2321 or #2322 #2323
[instance] 0x56096213b9b8 ; 1
[assign] (not #2323) justification -1: 272 -273
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2323
[conflict] #2323
[pop] 1 3
[assign] #2323 axiom
[assign] #1255 clause 273 -404
[assign] #2014 bin 273
[decide-and-or] #2017 #1301
[push] 2
[assign] (not #1287) decision axiom
[eq-expl] #798 root
[new-match] 0x56096213ba18 #29 #28 #798 ; #1287
[mk-app] #2322 = #1287 #1267
[mk-app] #2321 not #29
[mk-app] #2312 or #2321 #2322
[instance] 0x56096213ba18 ; 1
[assign] (not #2322) justification -1: 275 -278
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2322
[conflict] #2322
[pop] 1 3
[assign] #2322 axiom
[assign] #1287 clause 278 -405
[assign] #2022 bin 278
[decide-and-or] #1329 #1328
[push] 2
[assign] (not #1316) decision axiom
[eq-expl] #799 root
[new-match] 0x56096213ba78 #29 #28 #799 ; #1316
[mk-app] #2321 = #1316 #1315
[mk-app] #2312 not #29
[mk-app] #2327 or #2312 #2321
[instance] 0x56096213ba78 ; 1
[assign] (not #2321) justification -1: 282 -283
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2321
[conflict] #2321
[pop] 1 3
[assign] #2321 axiom
[assign] #1316 clause 283 -406
[assign] #1326 bin 283
[decide-and-or] #1365 #1364
[push] 2
[assign] (not #1352) decision axiom
[eq-expl] #800 root
[new-match] 0x56096213bad8 #29 #28 #800 ; #1352
[mk-app] #2312 = #1352 #1330
[mk-app] #2327 not #29
[mk-app] #2328 or #2327 #2312
[instance] 0x56096213bad8 ; 1
[assign] (not #2312) justification -1: 285 -288
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2312
[conflict] #2312
[pop] 1 3
[assign] #2312 axiom
[assign] #1352 clause 288 -407
[assign] #1363 bin 288
[decide-and-or] #1385 #1384
[push] 2
[assign] (not #1379) decision axiom
[eq-expl] #817 root
[new-match] 0x56096213bb38 #29 #28 #817 ; #1379
[mk-app] #2327 = #1379 #1378
[mk-app] #2328 not #29
[mk-app] #2329 or #2328 #2327
[instance] 0x56096213bb38 ; 1
[assign] (not #2327) justification -1: 292 -293
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2327
[conflict] #2327
[pop] 1 3
[assign] #2327 axiom
[assign] #1379 clause 293 -408
[assign] #1382 bin 293
[mk-app] #2328 <= #1380 #1381
[mk-app] #2329 >= #1380 #1381
[assign] #2328 justification -1: 294
[assign] #2329 justification -1: 294
[decide-and-or] #1395 #1394
[push] 2
[assign] (not #1388) decision axiom
[eq-expl] #801 root
[new-match] 0x56096213bc70 #29 #28 #801 ; #1388
[mk-app] #2330 = #1388 #1387
[mk-app] #2331 not #29
[mk-app] #2332 or #2331 #2330
[instance] 0x56096213bc70 ; 1
[assign] (not #2330) justification -1: 296 -297
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2330
[conflict] #2330
[pop] 1 3
[assign] #2330 axiom
[assign] #1388 clause 297 -411
[assign] #1392 bin 297
[decide-and-or] #2032 #1416
[push] 2
[assign] (not #1397) decision axiom
[eq-expl] #802 root
[new-match] 0x56096213bcd0 #29 #28 #802 ; #1397
[mk-app] #2331 = #1397 #1396
[mk-app] #2332 not #29
[mk-app] #2333 or #2332 #2331
[instance] 0x56096213bcd0 ; 1
[assign] (not #2331) justification -1: 299 -300
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2331
[conflict] #2331
[pop] 1 3
[assign] #2331 axiom
[assign] #1397 clause 300 -412
[assign] #2029 bin 300
[decide-and-or] #1433 #1432
[push] 2
[assign] (not #1419) decision axiom
[eq-expl] #803 root
[new-match] 0x56096214a8f8 #29 #28 #803 ; #1419
[mk-app] #2332 = #1419 #1418
[mk-app] #2333 not #29
[mk-app] #2334 or #2333 #2332
[instance] 0x56096214a8f8 ; 1
[assign] (not #2332) justification -1: 302 -303
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2332
[conflict] #2332
[pop] 1 3
[assign] #2332 axiom
[assign] #1419 clause 303 -413
[assign] #1431 bin 303
[decide-and-or] #2041 #1468
[push] 2
[assign] (not #1435) decision axiom
[eq-expl] #804 root
[new-match] 0x56096214a958 #29 #28 #804 ; #1435
[mk-app] #2333 = #1435 #1434
[mk-app] #2334 not #29
[mk-app] #2335 or #2334 #2333
[instance] 0x56096214a958 ; 1
[assign] (not #2333) justification -1: 305 -306
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2333
[conflict] #2333
[pop] 1 3
[assign] #2333 axiom
[assign] #1435 clause 306 -414
[assign] #2038 bin 306
[decide-and-or] #1478 #1477
[push] 2
[assign] (not #1471) decision axiom
[eq-expl] #805 root
[new-match] 0x56096214a9b8 #29 #28 #805 ; #1471
[mk-app] #2334 = #1471 #1470
[mk-app] #2335 not #29
[mk-app] #2336 or #2335 #2334
[instance] 0x56096214a9b8 ; 1
[assign] (not #2334) justification -1: 308 -309
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2334
[conflict] #2334
[pop] 1 3
[assign] #2334 axiom
[assign] #1471 clause 309 -415
[assign] #1475 bin 309
[decide-and-or] #1487 #1486
[push] 2
[assign] (not #1480) decision axiom
[eq-expl] #806 root
[new-match] 0x56096214aa18 #29 #28 #806 ; #1480
[mk-app] #2335 = #1480 #1479
[mk-app] #2336 not #29
[mk-app] #2337 or #2336 #2335
[instance] 0x56096214aa18 ; 1
[assign] (not #2335) justification -1: 311 -312
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2335
[conflict] #2335
[pop] 1 3
[assign] #2335 axiom
[assign] #1480 clause 312 -416
[assign] #1484 bin 312
[decide-and-or] #1501 #1500
[push] 2
[assign] (not #1489) decision axiom
[eq-expl] #807 root
[new-match] 0x56096214aa78 #29 #28 #807 ; #1489
[mk-app] #2336 = #1489 #1488
[mk-app] #2337 not #29
[mk-app] #2338 or #2337 #2336
[instance] 0x56096214aa78 ; 1
[assign] (not #2336) justification -1: 314 -315
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2336
[conflict] #2336
[pop] 1 3
[assign] #2336 axiom
[assign] #1489 clause 315 -417
[assign] #1498 bin 315
[decide-and-or] #1516 #1515
[push] 2
[assign] (not #1503) decision axiom
[eq-expl] #808 root
[new-match] 0x56096214aad8 #29 #28 #808 ; #1503
[mk-app] #2337 = #1503 #1502
[mk-app] #2338 not #29
[mk-app] #2339 or #2338 #2337
[instance] 0x56096214aad8 ; 1
[assign] (not #2337) justification -1: 317 -318
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2337
[conflict] #2337
[pop] 1 3
[assign] #2337 axiom
[assign] #1503 clause 318 -418
[assign] #1514 bin 318
[decide-and-or] #1525 #1528
[push] 2
[assign] (not #1518) decision axiom
[eq-expl] #809 root
[new-match] 0x56096214ab38 #29 #28 #809 ; #1518
[mk-app] #2338 = #1518 #1517
[mk-app] #2339 not #29
[mk-app] #2340 or #2339 #2338
[instance] 0x56096214ab38 ; 1
[assign] (not #2338) justification -1: 320 -321
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2338
[conflict] #2338
[pop] 1 3
[assign] #2338 axiom
[assign] #1518 clause 321 -419
[assign] #1531 bin 321
[decide-and-or] #1544 #1543
[push] 2
[assign] (not #1532) decision axiom
[eq-expl] #810 root
[new-match] 0x56096214ab98 #29 #28 #810 ; #1532
[mk-app] #2339 = #1532 #1526
[mk-app] #2340 not #29
[mk-app] #2341 or #2340 #2339
[instance] 0x56096214ab98 ; 1
[assign] (not #2339) justification -1: 323 -324
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2339
[conflict] #2339
[pop] 1 3
[assign] #2339 axiom
[assign] #1532 clause 324 -420
[assign] #1541 bin 324
[decide-and-or] #1559 #1558
[push] 2
[assign] (not #1546) decision axiom
[eq-expl] #811 root
[new-match] 0x56096214abf8 #29 #28 #811 ; #1546
[mk-app] #2340 = #1546 #1545
[mk-app] #2341 not #29
[mk-app] #2342 or #2341 #2340
[instance] 0x56096214abf8 ; 1
[assign] (not #2340) justification -1: 326 -327
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2340
[conflict] #2340
[pop] 1 3
[assign] #2340 axiom
[assign] #1546 clause 327 -421
[assign] #1557 bin 327
[decide-and-or] #1572 #1571
[push] 2
[assign] (not #1561) decision axiom
[eq-expl] #812 root
[new-match] 0x56096214ac58 #29 #28 #812 ; #1561
[mk-app] #2341 = #1561 #1560
[mk-app] #2342 not #29
[mk-app] #2343 or #2342 #2341
[instance] 0x56096214ac58 ; 1
[assign] (not #2341) justification -1: 329 -330
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2341
[conflict] #2341
[pop] 1 3
[assign] #2341 axiom
[assign] #1561 clause 330 -422
[assign] #1570 bin 330
[decide-and-or] #1582 #1581
[push] 2
[assign] (not #1574) decision axiom
[eq-expl] #813 root
[new-match] 0x56096214acb8 #29 #28 #813 ; #1574
[mk-app] #2342 = #1574 #1573
[mk-app] #2343 not #29
[mk-app] #2344 or #2343 #2342
[instance] 0x56096214acb8 ; 1
[assign] (not #2342) justification -1: 332 -333
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2342
[conflict] #2342
[pop] 1 3
[assign] #2342 axiom
[assign] #1574 clause 333 -423
[assign] #1579 bin 333
[decide-and-or] #1613 #1612
[push] 2
[assign] (not #1590) decision axiom
[eq-expl] #814 root
[new-match] 0x56096214ad18 #29 #28 #814 ; #1590
[mk-app] #2343 = #1590 #1589
[mk-app] #2344 not #29
[mk-app] #2345 or #2344 #2343
[instance] 0x56096214ad18 ; 1
[assign] (not #2343) justification -1: 336 -337
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2343
[conflict] #2343
[pop] 1 3
[assign] #2343 axiom
[assign] #1590 clause 337 -424
[assign] #1611 bin 337
[decide-and-or] #1641 #1640
[push] 2
[assign] (not #1615) decision axiom
[eq-expl] #815 root
[new-match] 0x56096214ad78 #29 #28 #815 ; #1615
[mk-app] #2344 = #1615 #1614
[mk-app] #2345 not #29
[mk-app] #2346 or #2345 #2344
[instance] 0x56096214ad78 ; 1
[assign] (not #2344) justification -1: 339 -340
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2344
[conflict] #2344
[pop] 1 3
[assign] #2344 axiom
[assign] #1615 clause 340 -425
[assign] #1639 bin 340
[decide-and-or] #1669 #1668
[push] 2
[assign] (not #1643) decision axiom
[eq-expl] #816 root
[new-match] 0x56096214add8 #29 #28 #816 ; #1643
[mk-app] #2345 = #1643 #1642
[mk-app] #2346 not #29
[mk-app] #2347 or #2346 #2345
[instance] 0x56096214add8 ; 1
[assign] (not #2345) justification -1: 342 -343
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2345
[conflict] #2345
[pop] 1 3
[assign] #2345 axiom
[assign] #1643 clause 343 -426
[assign] #1667 bin 343
[push] 2
[assign] (not #2199) decision axiom
[assign] (not #2308) clause -373 372
[assign] #2206 clause 375 372
[assign] #2307 clause 396 372
[eq-expl] #2204 root
[new-match] 0x56096214ae88 #1816 #344 #2204 ; #2205
[eq-expl] #2193 root
[eq-expl] #292 root
[new-match] 0x56096214aeb8 #563 #555 #292 #2193 ; #2204
[mk-app] #2346 >= #2205 #337
[mk-app] #2347 not #2346
[mk-app] #2348 >= #2204 #337
[mk-app] #2349 not #2348
[mk-app] #2350 = #2204 #2205
[mk-app] #2351 or #2349 #2350
[mk-app] #2352 not #2351
[mk-app] #2353 or #2347 #2352
[mk-app] #2354 not #2353
[mk-app] #2355 not #1816
[mk-app] #2356 or #2355 #2354
[instance] 0x56096214ae88 ; 1
[attach-enode] #2350 1
[attach-meaning] #366 arith (- 1)
[mk-app] #2357 * #366 #2205
[mk-app] #2358 + #2204 #2357
[mk-app] #2359 <= #2358 #337
[mk-app] #2360 >= #2358 #337
[attach-enode] #2357 1
[attach-enode] #2358 1
[assign] (not #2353) justification -1: 55
[end-of-instance]
[mk-app] #2361 * #366 #2193
[mk-app] #2362 + #292 #2361 #2204
[mk-app] #2363 = #2362 #337
[attach-meaning] #366 arith (- 1)
[mk-app] #2364 + #2361 #2204
[attach-meaning] #366 arith (- 1)
[mk-app] #2365 * #366 #2204
[mk-app] #2366 + #2193 #2365
[mk-app] #2364 = #2366 #292
[inst-discovered] theory-solving 0 arith# ; #2363
[mk-app] #2367 = #2363 #2364
[instance] 0 #2367
[attach-enode] #2367 0
[end-of-instance]
[mk-app] #2367 not #563
[mk-app] #2368 or #2367 #2364
[instance] 0x56096214aeb8 ; 1
[attach-enode] #2365 1
[attach-enode] #2366 1
[attach-enode] #2364 1
[mk-app] #2369 <= #2366 #292
[mk-app] #2370 >= #2366 #292
[assign] #2364 justification -1: 77
[end-of-instance]
[assign] #2346 clause 427 433
[assign] #2351 clause 432 433
[assign] #2369 clause 435 -434
[assign] #2370 clause 436 -434
[assign] #2348 clause 428 373 -435
[assign] #2350 clause 429 -428 -432
[assign] #2359 clause 430 -429
[assign] #2360 clause 431 -429
[decide-and-or] #2324 #2200
[push] 3
[assign] #2200 decision axiom
[assign] #2277 clause 391 -374
[decide-and-or] #2307 #2305
[push] 4
[assign] (not #2294) decision axiom
[assign] #2207 clause 376 378
[assign] (not #2293) clause -377 378
[eq-expl] #2203 lit #2206 ; #2205
[eq-expl] #2205 root
[eq-expl] #2208 cg (#2203 #2205) ; #2230
[eq-expl] #2230 root
[eq-expl] #2228 root
[eq-expl] #2 root
[new-match] 0x56096214b4d8 #1905 #765 #2 #2228 #2208 ; #2293
[new-match] 0x56096214b518 #170 #169 #2193 ; #2228
[new-match] 0x56096214b548 #170 #169 #2205 ; #2230
[mk-app] #2371 check_decrease_height #2230 #2228 #2
[mk-app] #2372 height #2230
[mk-app] #2373 height #2228
[mk-app] #2374 height_lt #2372 #2373
[mk-app] #2375 = #2372 #2373
[mk-app] #2376 not #2375
[mk-app] #2377 not #2
[mk-app] #2378 or #2376 #2377
[mk-app] #2379 not #2378
[mk-app] #2380 or #2374 #2379
[mk-app] #2381 = #2371 #2380
[inst-discovered] theory-solving 0 basic# ; #2377
[mk-app] #2382 = #2377 #1
[instance] 0 #2382
[attach-enode] #2382 0
[end-of-instance]
[mk-app] #2382 or #2376 #1
[inst-discovered] theory-solving 0 basic# ; #2382
[mk-app] #2383 = #2382 #1
[instance] 0 #2383
[attach-enode] #2383 0
[end-of-instance]
[mk-app] #2382 not #1
[inst-discovered] theory-solving 0 basic# ; #2382
[mk-app] #2383 = #2382 #2
[instance] 0 #2383
[attach-enode] #2383 0
[end-of-instance]
[mk-app] #2382 or #2374 #2
[inst-discovered] theory-solving 0 basic# ; #2382
[mk-app] #2383 = #2382 #2374
[instance] 0 #2383
[attach-enode] #2383 0
[end-of-instance]
[mk-app] #2382 = #2371 #2374
[mk-app] #2383 not #1905
[mk-app] #2384 or #2383 #2382
[instance] 0x56096214b4d8 ; 1
[attach-enode] #2371 1
[attach-enode] #2372 1
[attach-enode] #2373 1
[attach-enode] #2374 1
[assign] #2382 justification -1: 97
[end-of-instance]
[mk-app] #2385 %I #2228
[mk-app] #2386 = #2193 #2385
[mk-app] #2387 not #170
[mk-app] #2388 or #2387 #2386
[instance] 0x56096214b518 ; 1
[attach-enode] #2385 1
[attach-enode] #2386 1
[assign] #2386 justification -1: 25
[end-of-instance]
[mk-app] #2389 %I #2230
[mk-app] #2390 = #2205 #2389
[mk-app] #2391 or #2387 #2390
[instance] 0x56096214b548 ; 1
[attach-enode] #2389 1
[attach-enode] #2390 1
[assign] #2390 justification -1: 25
[end-of-instance]
[assign] (not #2371) justification -1: -377 375
[eq-expl] #2372 root
[eq-expl] #2373 root
[new-match] 0x56096214bab8 #1907 #774 #2193 #2205 ; #2374 (#2372 #2372) (#2373 #2373) (#2230 #2230) (#2228 #2228)
[new-match] 0x56096214baf0 #1912 #790 #2373 #2372 ; #2374
[mk-app] #2392 + #2193 #2357
[mk-app] #2393 <= #2392 #337
[mk-app] #2394 or #2347 #2393
[mk-app] #2395 = #2394 #2374
[mk-app] #2396 not #2395
[mk-app] #2397 not #2394
[inst-discovered] theory-solving 0 basic# ; #2396
[mk-app] #2397 = #2396 #2396
[instance] 0 #2397
[attach-enode] #2397 0
[end-of-instance]
[mk-app] #2397 not #1907
[mk-app] #2398 or #2397 #2396
[instance] 0x56096214bab8 ; 2
[attach-enode] #2392 2
[assign] (not #2395) justification -1: 98
[end-of-instance]
[mk-app] #2399 partial-order #2372 #2373
[mk-app] #2400 not #2399
[mk-app] #2401 or #2400 #2375
[mk-app] #2402 = #2401 #2374
[mk-app] #2403 not #2402
[mk-app] #2404 not #2401
[inst-discovered] theory-solving 0 basic# ; #2403
[mk-app] #2404 = #2403 #2403
[instance] 0 #2404
[attach-enode] #2404 0
[end-of-instance]
[mk-app] #2404 not #1912
[mk-app] #2405 or #2404 #2403
[instance] 0x56096214baf0 ; 2
[attach-enode] #2375 2
[assign] (not #2402) justification -1: 99
[end-of-instance]
[assign] (not #2374) clause -438 437 -439
[assign] #2394 clause 443 438 444
[assign] #2401 clause 447 438 448
[assign] #2393 clause 442 -443
[resolve-process] true
[resolve-lit] 2 (not #2360)
[resolve-lit] 0 (not #2393)
[resolve-lit] 2 (not #2370)
[conflict] (not #2393) (not #2360)
[pop] 2 5
[attach-enode] #2392 0
[assign] (not #2393) clause -437 -431
[decide-and-or] #2324 #2200
[push] 3
[assign] #2200 decision axiom
[assign] #2277 clause 391 -374
[decide-and-or] #2307 #2305
[push] 4
[assign] (not #2294) decision axiom
[assign] #2207 clause 376 378
[assign] (not #2293) clause -377 378
[new-match] 0x56096214b570 #1905 #765 #2 #2228 #2208 ; #2293
[new-match] 0x56096214b5b0 #170 #169 #2193 ; #2228
[new-match] 0x56096214b5e0 #170 #169 #2205 ; #2230
[inst-discovered] theory-solving 0 basic# ; #2377
[mk-app] #2382 = #2377 #1
[instance] 0 #2382
[attach-enode] #2382 0
[end-of-instance]
[mk-app] #2382 or #2376 #1
[inst-discovered] theory-solving 0 basic# ; #2382
[mk-app] #2404 = #2382 #1
[instance] 0 #2404
[attach-enode] #2404 0
[end-of-instance]
[mk-app] #2382 not #1
[inst-discovered] theory-solving 0 basic# ; #2382
[mk-app] #2404 = #2382 #2
[instance] 0 #2404
[attach-enode] #2404 0
[end-of-instance]
[mk-app] #2382 or #2374 #2
[inst-discovered] theory-solving 0 basic# ; #2382
[mk-app] #2404 = #2382 #2374
[instance] 0 #2404
[attach-enode] #2404 0
[end-of-instance]
[mk-app] #2382 = #2371 #2374
[mk-app] #2404 not #1905
[mk-app] #2405 or #2404 #2382
[instance] 0x56096214b570 ; 1
[attach-enode] #2371 1
[attach-enode] #2372 1
[attach-enode] #2373 1
[attach-enode] #2374 1
[assign] #2382 justification -1: 97
[end-of-instance]
[mk-app] #2397 not #170
[mk-app] #2398 or #2397 #2386
[instance] 0x56096214b5b0 ; 1
[attach-enode] #2385 1
[attach-enode] #2386 1
[assign] #2386 justification -1: 25
[end-of-instance]
[mk-app] #2387 or #2397 #2390
[instance] 0x56096214b5e0 ; 1
[attach-enode] #2389 1
[attach-enode] #2390 1
[assign] #2390 justification -1: 25
[end-of-instance]
[assign] (not #2371) justification -1: -377 375
[eq-expl] #2372 root
[eq-expl] #2373 root
[new-match] 0x56096214bb50 #1907 #774 #2193 #2205 ; #2374 (#2372 #2372) (#2373 #2373) (#2230 #2230) (#2228 #2228)
[new-match] 0x56096214bb88 #1912 #790 #2373 #2372 ; #2374
[mk-app] #2391 not #2394
[inst-discovered] theory-solving 0 basic# ; #2396
[mk-app] #2391 = #2396 #2396
[instance] 0 #2391
[attach-enode] #2391 0
[end-of-instance]
[mk-app] #2391 not #1907
[mk-app] #2388 or #2391 #2396
[instance] 0x56096214bb50 ; 2
[assign] (not #2394) justification -1: 427 -437
[assign] (not #2395) justification -1: 98
[end-of-instance]
[mk-app] #2383 not #2401
[inst-discovered] theory-solving 0 basic# ; #2403
[mk-app] #2383 = #2403 #2403
[instance] 0 #2383
[attach-enode] #2383 0
[end-of-instance]
[mk-app] #2383 not #1912
[mk-app] #2384 or #2383 #2403
[instance] 0x56096214bb88 ; 2
[attach-enode] #2375 2
[assign] (not #2402) justification -1: 99
[end-of-instance]
[assign] (not #2374) clause -439 438 -440
[resolve-process] true
[resolve-lit] 0 #2374
[resolve-lit] 0 #2395
[resolve-lit] 0 #2394
[resolve-process] #2374
[resolve-lit] 0 #2371
[resolve-lit] 0 (not #2382)
[resolve-process] #2395
[resolve-process] #2394
[resolve-lit] 2 (not #2346)
[resolve-lit] 2 #2393
[resolve-process] #2371
[resolve-lit] 0 #2293
[resolve-lit] 2 (not #2206)
[resolve-process] (not #2382)
[conflict] #2293 #2393 (not #2206)
[pop] 2 5
[assign] #2293 clause 377 437 -375
[assign] #2294 clause 378 -377
[assign] (not #2304) clause -395 -378 -396
[assign] #2212 clause 379 395
[assign] #2224 clause 382 395
[assign] #2302 clause 394 395
[new-match] 0x56096214b540 #1905 #765 #2 #2228 #2208 ; #2293
[new-match] 0x56096214b580 #170 #169 #2193 ; #2228
[new-match] 0x56096214b5b0 #170 #169 #2205 ; #2230
[eq-expl] #2215 root
[new-match] 0x56096214b5e0 #170 #169 #2215 ; #2216
[eq-expl] #2219 root
[new-match] 0x56096214b610 #170 #169 #2219 ; #2220
[eq-expl] #2191 root
[new-match] 0x56096214b640 #1794 #1793 #2203 #2191 ; #2212
[eq-expl] #1196 root
[eq-expl] #2221 root
[new-match] 0x56096214b678 #570 #564 #2221 #1196 ; #2222
[new-match] 0x56096214b6b0 #1865 #564 #2221 #1196 ; #2222
[eq-expl] #2216 root
[new-match] 0x56096214b6e8 #1221 #1217 #2216 ; #2217
[eq-expl] #2220 root
[new-match] 0x56096214b718 #1221 #1217 #2220 ; #2221
[eq-expl] #2214 root
[new-match] 0x56096214b748 #1816 #344 #2214 ; #2215
[eq-expl] #2218 root
[new-match] 0x56096214b778 #1816 #344 #2218 ; #2219
[new-match] 0x56096214b7a8 #548 #546 #2193 #2191 ; #2214
[new-match] 0x56096214b7e0 #563 #555 #292 #2215 ; #2218
[inst-discovered] theory-solving 0 basic# ; #2377
[mk-app] #2382 = #2377 #1
[instance] 0 #2382
[attach-enode] #2382 0
[end-of-instance]
[mk-app] #2382 or #2376 #1
[inst-discovered] theory-solving 0 basic# ; #2382
[mk-app] #2383 = #2382 #1
[instance] 0 #2383
[attach-enode] #2383 0
[end-of-instance]
[mk-app] #2382 not #1
[inst-discovered] theory-solving 0 basic# ; #2382
[mk-app] #2383 = #2382 #2
[instance] 0 #2383
[attach-enode] #2383 0
[end-of-instance]
[mk-app] #2382 or #2374 #2
[inst-discovered] theory-solving 0 basic# ; #2382
[mk-app] #2383 = #2382 #2374
[instance] 0 #2383
[attach-enode] #2383 0
[end-of-instance]
[mk-app] #2382 = #2371 #2374
[mk-app] #2383 not #1905
[mk-app] #2384 or #2383 #2382
[instance] 0x56096214b540 ; 1
[attach-enode] #2371 1
[attach-enode] #2372 1
[attach-enode] #2373 1
[attach-enode] #2374 1
[assign] #2382 justification -1: 97
[end-of-instance]
[mk-app] #2391 not #170
[mk-app] #2388 or #2391 #2386
[instance] 0x56096214b580 ; 1
[attach-enode] #2385 1
[attach-enode] #2386 1
[assign] #2386 justification -1: 25
[end-of-instance]
[mk-app] #2397 or #2391 #2390
[instance] 0x56096214b5b0 ; 1
[attach-enode] #2389 1
[attach-enode] #2390 1
[assign] #2390 justification -1: 25
[end-of-instance]
[mk-app] #2387 %I #2216
[mk-app] #2398 = #2215 #2387
[mk-app] #2404 or #2391 #2398
[instance] 0x56096214b5e0 ; 1
[attach-enode] #2387 1
[attach-enode] #2398 1
[assign] #2398 justification -1: 25
[end-of-instance]
[mk-app] #2405 %I #2220
[mk-app] #2406 = #2219 #2405
[mk-app] #2407 or #2391 #2406
[instance] 0x56096214b610 ; 1
[attach-enode] #2405 1
[attach-enode] #2406 1
[assign] #2406 justification -1: 25
[end-of-instance]
[mk-app] #2408 ens%the_q!model.lemma_pow2_add. #2191 #2205
[mk-app] #2409 Add #2191 #2205
[mk-app] #2410 nClip #2409
[mk-app] #2411 I #2410
[mk-app] #2412 the_q!model.pow2.? #2411
[mk-app] #2413 = #2412 #2241
[mk-app] #2414 = #2408 #2413
[mk-app] #2415 not #1794
[mk-app] #2416 or #2415 #2414
[instance] 0x56096214b640 ; 1
[attach-enode] #2408 1
[attach-enode] #2409 1
[attach-enode] #2410 1
[attach-enode] #2411 1
[attach-enode] #2412 1
[attach-enode] #2413 1
[assign] #2414 justification -1: 360
[end-of-instance]
[mk-app] #2417 * #2221 #1196
[mk-app] #2418 * #366 #2417
[mk-app] #2419 + #2222 #2418
[mk-app] #2420 = #2419 #337
[mk-app] #2421 * #1196 #2221
[inst-discovered] theory-solving 0 arith# ; #2417
[mk-app] #2422 = #2417 #2421
[instance] 0 #2422
[attach-enode] #2422 0
[end-of-instance]
[mk-app] #2422 Int
[attach-meaning] #2422 arith (- 2)
[mk-app] #2423 * #2422 #2221
[mk-app] #2424 * #366 #2421
[inst-discovered] theory-solving 0 arith# ; #2424
[mk-app] #2425 = #2424 #2423
[instance] 0 #2425
[attach-enode] #2425 0
[end-of-instance]
[mk-app] #2421 + #2423 #2222
[mk-app] #2424 + #2222 #2423
[inst-discovered] theory-solving 0 arith# ; #2424
[mk-app] #2425 = #2424 #2421
[instance] 0 #2425
[attach-enode] #2425 0
[end-of-instance]
[mk-app] #2424 * #1196 #2221
[attach-meaning] #366 arith (- 1)
[mk-app] #2425 * #366 #2222
[mk-app] #2426 + #2424 #2425
[mk-app] #2427 = #2426 #337
[mk-app] #2428 = #2421 #337
[inst-discovered] theory-solving 0 arith# ; #2428
[mk-app] #2429 = #2428 #2427
[instance] 0 #2429
[attach-enode] #2429 0
[end-of-instance]
[mk-app] #2422 not #570
[mk-app] #2423 or #2422 #2427
[instance] 0x56096214b678 ; 1
[attach-enode] #2424 1
[attach-enode] #2425 1
[attach-enode] #2426 1
[attach-enode] #2427 1
[mk-app] #2421 <= #2426 #337
[mk-app] #2428 >= #2426 #337
[assign] #2427 justification -1: 78
[end-of-instance]
[mk-app] #2429 >= #1196 #337
[mk-app] #2430 not #2429
[mk-app] #2431 >= #2221 #337
[mk-app] #2432 not #2431
[mk-app] #2433 >= #2222 #337
[mk-app] #2434 or #2430 #2432 #2433
[mk-app] #2435 Int
[attach-meaning] #2435 arith (- 2)
[inst-discovered] theory-solving 0 arith# ; #2429
[mk-app] #2435 = #2429 #1
[instance] 0 #2435
[attach-enode] #2435 0
[end-of-instance]
[mk-app] #2435 not #1
[inst-discovered] theory-solving 0 basic# ; #2435
[mk-app] #2436 = #2435 #2
[instance] 0 #2436
[attach-enode] #2436 0
[end-of-instance]
[mk-app] #2435 or #2432 #2433
[mk-app] #2436 or #2 #2432 #2433
[inst-discovered] theory-solving 0 basic# ; #2436
[mk-app] #2437 = #2436 #2435
[instance] 0 #2437
[attach-enode] #2437 0
[end-of-instance]
[mk-app] #2436 not #1865
[mk-app] #2437 or #2436 #2432 #2433
[instance] 0x56096214b6b0 ; 1
[end-of-instance]
[mk-app] #2435 has_type #2216 #196
[mk-app] #2438 not #2435
[mk-app] #2439 the_q!model.rec%pow2.? #2216 #1213
[mk-app] #2440 = #2217 #2439
[mk-app] #2441 or #2438 #2440
[mk-app] #2442 not #1221
[mk-app] #2443 or #2442 #2438 #2440
[instance] 0x56096214b6e8 ; 1
[attach-enode] #2435 1
[attach-enode] #1212 1
[attach-enode] #1213 1
[attach-enode] #2439 1
[attach-enode] #2440 1
[end-of-instance]
[mk-app] #2444 has_type #2220 #196
[mk-app] #2445 not #2444
[mk-app] #2446 the_q!model.rec%pow2.? #2220 #1213
[mk-app] #2447 = #2221 #2446
[mk-app] #2448 or #2445 #2447
[mk-app] #2449 or #2442 #2445 #2447
[instance] 0x56096214b718 ; 1
[attach-enode] #2444 1
[attach-enode] #2446 1
[attach-enode] #2447 1
[end-of-instance]
[mk-app] #2450 >= #2215 #337
[mk-app] #2451 not #2450
[mk-app] #2452 >= #2214 #337
[mk-app] #2453 not #2452
[mk-app] #2454 = #2214 #2215
[mk-app] #2455 or #2453 #2454
[mk-app] #2456 not #2455
[mk-app] #2457 or #2451 #2456
[mk-app] #2458 not #2457
[mk-app] #2459 or #2355 #2458
[instance] 0x56096214b748 ; 1
[attach-enode] #2454 1
[attach-meaning] #366 arith (- 1)
[mk-app] #2460 * #366 #2215
[mk-app] #2461 + #2214 #2460
[mk-app] #2462 <= #2461 #337
[mk-app] #2463 >= #2461 #337
[attach-enode] #2460 1
[attach-enode] #2461 1
[assign] (not #2457) justification -1: 55
[end-of-instance]
[mk-app] #2464 >= #2219 #337
[mk-app] #2465 not #2464
[mk-app] #2466 >= #2218 #337
[mk-app] #2467 not #2466
[mk-app] #2468 = #2218 #2219
[mk-app] #2469 or #2467 #2468
[mk-app] #2470 not #2469
[mk-app] #2471 or #2465 #2470
[mk-app] #2472 not #2471
[mk-app] #2473 or #2355 #2472
[instance] 0x56096214b778 ; 1
[attach-enode] #2468 1
[attach-meaning] #366 arith (- 1)
[mk-app] #2474 * #366 #2219
[mk-app] #2475 + #2218 #2474
[mk-app] #2476 <= #2475 #337
[mk-app] #2477 >= #2475 #337
[attach-enode] #2474 1
[attach-enode] #2475 1
[assign] (not #2471) justification -1: 55
[end-of-instance]
[mk-app] #2478 * #366 #2214
[mk-app] #2479 + #2193 #2191 #2478
[mk-app] #2480 = #2479 #337
[mk-app] #2481 + #2191 #2193 #2478
[inst-discovered] theory-solving 0 arith# ; #2479
[mk-app] #2482 = #2479 #2481
[instance] 0 #2482
[attach-enode] #2482 0
[end-of-instance]
[mk-app] #2482 = #2481 #337
[mk-app] #2483 not #548
[mk-app] #2484 or #2483 #2482
[instance] 0x56096214b7a8 ; 1
[attach-enode] #2478 1
[attach-enode] #2481 1
[attach-enode] #2482 1
[mk-app] #2485 <= #2481 #337
[mk-app] #2486 >= #2481 #337
[assign] #2482 justification -1: 76
[end-of-instance]
[mk-app] #2487 + #292 #2460 #2218
[mk-app] #2488 = #2487 #337
[attach-meaning] #366 arith (- 1)
[mk-app] #2489 + #2460 #2218
[attach-meaning] #366 arith (- 1)
[mk-app] #2490 * #366 #2218
[mk-app] #2491 + #2215 #2490
[mk-app] #2489 = #2491 #292
[inst-discovered] theory-solving 0 arith# ; #2488
[mk-app] #2492 = #2488 #2489
[instance] 0 #2492
[attach-enode] #2492 0
[end-of-instance]
[mk-app] #2492 or #2367 #2489
[instance] 0x56096214b7e0 ; 1
[attach-enode] #2490 1
[attach-enode] #2491 1
[attach-enode] #2489 1
[mk-app] #2493 <= #2491 #292
[mk-app] #2494 >= #2491 #292
[assign] #2489 justification -1: 77
[end-of-instance]
[assign] #2421 clause 449 -448
[assign] #2428 clause 450 -448
[assign] #2450 clause 457 463
[assign] #2455 clause 462 463
[assign] #2464 clause 464 470
[assign] #2469 clause 469 470
[assign] #2485 clause 472 -471
[assign] #2486 clause 473 -471
[assign] #2493 clause 475 -474
[assign] #2494 clause 476 -474
[assign] #2371 justification -1: 377 375
[assign] #2408 justification -1: 379 375
[assign] #2452 clause 458 -472 -369 -370
[eq-expl] #2372 root
[eq-expl] #2373 root
[new-match] 0x5609620f5808 #1907 #774 #2193 #2205 ; #2374 (#2372 #2372) (#2373 #2373) (#2230 #2230) (#2228 #2228)
[new-match] 0x5609620f5840 #1912 #790 #2373 #2372 ; #2374
[eq-expl] #2240 root
[eq-expl] #2231 root
[new-match] 0x5609620f5878 #570 #564 #2231 #2240 ; #2241
[new-match] 0x5609620f58b0 #1865 #564 #2231 #2240 ; #2241
[eq-expl] #2411 root
[new-match] 0x5609620f58e8 #1221 #1217 #2411 ; #2412
[new-match] 0x5609620f5918 #1221 #1217 #2230 ; #2231
[eq-expl] #2239 root
[new-match] 0x5609620f5948 #1221 #1217 #2239 ; #2240
[eq-expl] #2410 root
[new-match] 0x5609620f5978 #170 #169 #2410 ; #2411
[new-match] 0x5609620f59a8 #170 #169 #2191 ; #2239
[eq-expl] #2409 root
[new-match] 0x5609620f59d8 #1816 #344 #2409 ; #2410
[new-match] 0x5609620f5a08 #548 #546 #2205 #2191 ; #2409
[mk-app] #2495 not #2394
[inst-discovered] theory-solving 0 basic# ; #2396
[mk-app] #2495 = #2396 #2396
[instance] 0 #2495
[attach-enode] #2495 0
[end-of-instance]
[mk-app] #2495 not #1907
[mk-app] #2496 or #2495 #2396
[instance] 0x5609620f5808 ; 2
[assign] (not #2394) justification -1: 427 -437
[assign] (not #2395) justification -1: 98
[end-of-instance]
[mk-app] #2497 not #2401
[inst-discovered] theory-solving 0 basic# ; #2403
[mk-app] #2497 = #2403 #2403
[instance] 0 #2497
[attach-enode] #2497 0
[end-of-instance]
[mk-app] #2497 not #1912
[mk-app] #2498 or #2497 #2403
[instance] 0x5609620f5840 ; 2
[attach-enode] #2375 2
[assign] (not #2402) justification -1: 99
[end-of-instance]
[mk-app] #2499 * #2231 #2240
[mk-app] #2500 * #366 #2499
[mk-app] #2501 + #2241 #2500
[mk-app] #2502 = #2501 #337
[mk-app] #2503 or #2422 #2502
[instance] 0x5609620f5878 ; 1
[attach-enode] #2499 1
[attach-enode] #2500 1
[attach-enode] #2501 1
[attach-enode] #2502 1
[mk-app] #2504 <= #2501 #337
[mk-app] #2505 >= #2501 #337
[assign] #2502 justification -1: 78
[end-of-instance]
[mk-app] #2506 >= #2240 #337
[mk-app] #2507 not #2506
[mk-app] #2508 >= #2231 #337
[mk-app] #2509 not #2508
[mk-app] #2510 >= #2241 #337
[mk-app] #2511 or #2507 #2509 #2510
[mk-app] #2512 or #2436 #2507 #2509 #2510
[instance] 0x5609620f58b0 ; 1
[end-of-instance]
[mk-app] #2513 has_type #2411 #196
[mk-app] #2514 not #2513
[mk-app] #2515 the_q!model.rec%pow2.? #2411 #1213
[mk-app] #2516 = #2412 #2515
[mk-app] #2517 or #2514 #2516
[mk-app] #2518 or #2442 #2514 #2516
[instance] 0x5609620f58e8 ; 2
[attach-enode] #2513 2
[attach-enode] #2515 2
[attach-enode] #2516 2
[end-of-instance]
[mk-app] #2519 has_type #2230 #196
[mk-app] #2520 not #2519
[mk-app] #2521 the_q!model.rec%pow2.? #2230 #1213
[mk-app] #2522 = #2231 #2521
[mk-app] #2523 or #2520 #2522
[mk-app] #2524 or #2442 #2520 #2522
[instance] 0x5609620f5918 ; 1
[attach-enode] #2519 1
[attach-enode] #2521 1
[attach-enode] #2522 1
[end-of-instance]
[mk-app] #2525 has_type #2239 #196
[mk-app] #2526 not #2525
[mk-app] #2527 the_q!model.rec%pow2.? #2239 #1213
[mk-app] #2528 = #2240 #2527
[mk-app] #2529 or #2526 #2528
[mk-app] #2530 or #2442 #2526 #2528
[instance] 0x5609620f5948 ; 1
[attach-enode] #2525 1
[attach-enode] #2527 1
[attach-enode] #2528 1
[end-of-instance]
[mk-app] #2531 %I #2411
[mk-app] #2532 = #2410 #2531
[mk-app] #2533 or #2391 #2532
[instance] 0x5609620f5978 ; 2
[attach-enode] #2531 2
[attach-enode] #2532 2
[assign] #2532 justification -1: 25
[end-of-instance]
[mk-app] #2534 %I #2239
[mk-app] #2535 = #2191 #2534
[mk-app] #2536 or #2391 #2535
[instance] 0x5609620f59a8 ; 1
[attach-enode] #2534 1
[attach-enode] #2535 1
[assign] #2535 justification -1: 25
[end-of-instance]
[mk-app] #2537 >= #2410 #337
[mk-app] #2538 not #2537
[mk-app] #2539 >= #2409 #337
[mk-app] #2540 not #2539
[mk-app] #2541 = #2409 #2410
[mk-app] #2542 or #2540 #2541
[mk-app] #2543 not #2542
[mk-app] #2544 or #2538 #2543
[mk-app] #2545 not #2544
[mk-app] #2546 or #2355 #2545
[instance] 0x5609620f59d8 ; 2
[attach-enode] #2541 2
[attach-meaning] #366 arith (- 1)
[mk-app] #2547 * #366 #2410
[mk-app] #2548 + #2409 #2547
[mk-app] #2549 <= #2548 #337
[mk-app] #2550 >= #2548 #337
[attach-enode] #2547 2
[attach-enode] #2548 2
[assign] (not #2544) justification -1: 55
[end-of-instance]
[mk-app] #2551 * #366 #2409
[mk-app] #2552 + #2205 #2191 #2551
[mk-app] #2553 = #2552 #337
[mk-app] #2554 + #2191 #2205 #2551
[inst-discovered] theory-solving 0 arith# ; #2552
[mk-app] #2555 = #2552 #2554
[instance] 0 #2555
[attach-enode] #2555 0
[end-of-instance]
[mk-app] #2555 = #2554 #337
[mk-app] #2556 or #2483 #2555
[instance] 0x5609620f5a08 ; 2
[attach-enode] #2551 2
[attach-enode] #2554 2
[attach-enode] #2555 2
[mk-app] #2557 <= #2554 #337
[mk-app] #2558 >= #2554 #337
[assign] #2555 justification -1: 76
[end-of-instance]
[assign] #2374 clause 439 -438 -440
[assign] #2413 clause 446 -445 -447
[assign] #2454 clause 459 -458 -462
[assign] #2504 clause 484 -483
[assign] #2505 clause 485 -483
[assign] #2537 clause 497 503
[assign] #2542 clause 502 503
[assign] #2557 clause 505 -504
[assign] #2558 clause 506 -504
[assign] (not #2401) clause -481 -439 482
[assign] #2462 clause 460 -459
[assign] #2463 clause 461 -459
[assign] #2399 clause 479 481
[assign] (not #2375) clause -480 481
[assign] #2539 clause 498 -427 -369 -505
[assign] #2466 clause 465 373 -460 -369 -472 -475
[assign] #2541 clause 499 -498 -502
[assign] #2468 clause 466 -465 -469
[assign] #2549 clause 500 -499
[assign] #2550 clause 501 -499
[assign] #2476 clause 467 -466
[assign] #2477 clause 468 -466
[decide-and-or] #2324 #2200
[push] 3
[assign] #2200 decision axiom
[assign] #2277 clause 391 -374
[decide-and-or] #2302 #2300
[push] 4
[assign] (not #2271) decision axiom
[assign] #2225 clause 383 384
[assign] (not #2213) clause -380 384
[assign] (not #2223) clause -381 380 -382
[assign] #2295 clause 393 380
[decide-and-or] #2437 #2432
[push] 5
[assign] (not #2431) decision axiom
[assign] (not #2433) clause -452 451 -450
[decide-and-or] #2443 #2438
[push] 6
[assign] (not #2435) decision axiom
[eq-expl] #196 root
[new-match] 0x56096216b018 #518 #199 #2216 ; #2435 (#196 #196)
[new-match] 0x56096216b048 #203 #199 #2216 ; #2435 (#196 #196)
[eq-expl] #2215 lit #2398 ; #2387
[eq-expl] #2387 root
[new-match] 0x56096216b078 #469 #466 #2215 ; #2435 (#196 #196) (#2216 #2216)
[mk-app] #2559 >= #2387 #337
[mk-app] #2560 not #2559
[mk-app] #2561 I #2387
[mk-app] #2562 has_type #2561 #196
[mk-app] #2563 or #2560 #2562
[mk-app] #2564 not #469
[mk-app] #2565 or #2564 #2560 #2562
[instance] 0x56096216b078 ; 2
[attach-enode] #2561 2
[attach-enode] #2562 2
[end-of-instance]
[assign] (not #2562) justification -1: -453 443
[attach-meaning] #366 arith (- 1)
[mk-app] #2566 * #366 #2387
[mk-app] #2567 + #2215 #2566
[mk-app] #2568 <= #2567 #337
[mk-app] #2569 >= #2567 #337
[attach-enode] #2566 0
[attach-enode] #2567 0
[assign] #2568 justification -1: 443
[assign] #2569 justification -1: 443
[assign] (not #2559) clause -507 508
[resolve-process] true
[resolve-lit] 0 #2559
[resolve-lit] 4 (not #2462)
[resolve-lit] 4 (not #2485)
[resolve-lit] 0 (not #2568)
[resolve-process] #2559
[resolve-lit] 0 #2562
[resolve-process] (not #2568)
[resolve-lit] 4 (not #2398)
[conflict] #2562
[pop] 1 7
[attach-enode] #2561 0
[attach-enode] #2562 0
[assign] #2562 axiom
[assign] #2435 justification -1: 507 443
[new-match] 0x56096216b168 #518 #199 #2216 ; #2435 (#196 #196)
[new-match] 0x56096216b198 #203 #199 #2216 ; #2435 (#196 #196)
[new-match] 0x56096216b1c8 #469 #466 #2215 ; #2435 (#196 #196) (#2216 #2216)
[mk-app] #2566 or #2438 #2559
[mk-app] #2567 not #518
[mk-app] #2568 or #2567 #2438 #2559
[instance] 0x56096216b168 ; 2
[assign] #2559 justification -1: 70 453
[end-of-instance]
[assign] #2440 clause 454 -453
[attach-meaning] #366 arith (- 1)
[mk-app] #2569 * #366 #2387
[mk-app] #2564 + #2215 #2569
[mk-app] #2565 <= #2564 #337
[mk-app] #2570 >= #2564 #337
[attach-enode] #2569 0
[attach-enode] #2564 0
[assign] #2565 justification -1: 443
[assign] #2570 justification -1: 443
[eq-expl] #1213 root
[new-match] 0x56096216b440 #1191 #1190 #1213 #2216 ; #2439
[eq-expl] #1212 root
[new-match] 0x56096216b478 #1209 #1205 #1212 #2216 ; #2439 (#1213 #1213)
[mk-app] #2571 the_q!model.rec%pow2.? #2216 #1187
[mk-app] #2572 = #2439 #2571
[mk-app] #2573 not #1191
[mk-app] #2574 or #2573 #2572
[instance] 0x56096216b440 ; 2
[attach-enode] #1187 2
[attach-enode] #2571 2
[attach-enode] #2572 2
[assign] #2572 justification -1: 262
[end-of-instance]
[mk-app] #2575 = #2387 #337
[mk-app] #2576 Sub #2387 #292
[mk-app] #2577 nClip #2576
[mk-app] #2578 I #2577
[mk-app] #2579 the_q!model.rec%pow2.? #2578 #1212
[mk-app] #2580 Mul #1196 #2579
[mk-app] #2581 if #2575 #292 #2580
[mk-app] #2582 = #2439 #2581
[mk-app] #2583 or #2438 #2582
[mk-app] #2584 not #1209
[mk-app] #2585 or #2584 #2438 #2582
[instance] 0x56096216b478 ; 2
[mk-app] #2586 = #2581 #292
[mk-app] #2587 = #2580 #2581
[attach-enode] #2581 2
[attach-enode] #2575 2
[mk-app] #2588 <= #2387 #337
[attach-enode] #2576 2
[attach-enode] #2577 2
[attach-enode] #2578 2
[attach-enode] #2579 2
[attach-enode] #2580 2
[attach-enode] #2586 2
[attach-enode] #2587 2
[attach-enode] #2582 2
[assign] #2582 justification -1: 263 453
[end-of-instance]
[assign] (not #2588) clause -513 -509 -460 -472 373 -369
[eq-expl] #1187 root
[new-match] 0x56096216bd68 #1191 #1190 #1187 #2216 ; #2571
[assign] (not #2575) clause -512 513
[assign] #2587 clause 515 512
[eq-expl] #2579 root
[new-match] 0x56096216bdf0 #570 #564 #2579 #1196 ; #2580
[new-match] 0x56096216be28 #1865 #564 #2579 #1196 ; #2580
[eq-expl] #2576 cg (#2387 #2215) (#292 #292) ; #2218
[eq-expl] #2218 lit #2468 ; #2219
[eq-expl] #2219 lit #2406 ; #2405
[eq-expl] #2405 root
[eq-expl] #2577 cg (#2576 #2218) ; #2219
[eq-expl] #2578 cg (#2577 #2219) ; #2220
[new-match] 0x56096216be60 #1191 #1190 #1212 #2578 ; #2579
[mk-app] #2589 * #2579 #1196
[mk-app] #2590 * #366 #2589
[mk-app] #2591 + #2580 #2590
[mk-app] #2592 = #2591 #337
[mk-app] #2593 * #1196 #2579
[inst-discovered] theory-solving 0 arith# ; #2589
[mk-app] #2594 = #2589 #2593
[instance] 0 #2594
[attach-enode] #2594 0
[end-of-instance]
[mk-app] #2594 Int
[attach-meaning] #2594 arith (- 2)
[mk-app] #2595 * #2594 #2579
[mk-app] #2596 * #366 #2593
[inst-discovered] theory-solving 0 arith# ; #2596
[mk-app] #2597 = #2596 #2595
[instance] 0 #2597
[attach-enode] #2597 0
[end-of-instance]
[mk-app] #2593 + #2595 #2580
[mk-app] #2596 + #2580 #2595
[inst-discovered] theory-solving 0 arith# ; #2596
[mk-app] #2597 = #2596 #2593
[instance] 0 #2597
[attach-enode] #2597 0
[end-of-instance]
[mk-app] #2596 * #1196 #2579
[attach-meaning] #366 arith (- 1)
[mk-app] #2597 * #366 #2580
[mk-app] #2598 + #2596 #2597
[mk-app] #2599 = #2598 #337
[mk-app] #2600 = #2593 #337
[inst-discovered] theory-solving 0 arith# ; #2600
[mk-app] #2601 = #2600 #2599
[instance] 0 #2601
[attach-enode] #2601 0
[end-of-instance]
[mk-app] #2594 or #2422 #2599
[instance] 0x56096216bdf0 ; 3
[attach-enode] #2596 3
[attach-enode] #2597 3
[attach-enode] #2598 3
[attach-enode] #2599 3
[mk-app] #2595 <= #2598 #337
[mk-app] #2593 >= #2598 #337
[assign] #2599 justification -1: 78
[end-of-instance]
[mk-app] #2600 >= #2579 #337
[mk-app] #2601 not #2600
[mk-app] #2602 >= #2580 #337
[mk-app] #2603 or #2430 #2601 #2602
[mk-app] #2604 or #2601 #2602
[mk-app] #2605 or #2 #2601 #2602
[inst-discovered] theory-solving 0 basic# ; #2605
[mk-app] #2606 = #2605 #2604
[instance] 0 #2606
[attach-enode] #2606 0
[end-of-instance]
[mk-app] #2605 or #2436 #2601 #2602
[instance] 0x56096216be28 ; 3
[end-of-instance]
[mk-app] #2604 the_q!model.rec%pow2.? #2220 #1212
[mk-app] #2606 the_q!model.rec%pow2.? #2220 #1187
[mk-app] #2607 = #2604 #2606
[mk-app] #2608 or #2573 #2607
[instance] 0x56096216be60 ; 3
[attach-enode] #2604 3
[attach-enode] #2606 3
[attach-enode] #2607 3
[assign] #2607 justification -1: 262
[end-of-instance]
[assign] #2595 clause 518 -517
[assign] #2593 clause 519 -517
[mk-app] #2609 = #2222 #2580
[attach-meaning] #366 arith (- 1)
[mk-app] #2610 + #2222 #2597
[mk-app] #2611 <= #2610 #337
[mk-app] #2612 >= #2610 #337
[attach-enode] #2609 0
[attach-enode] #2610 0
[new-match] 0x56096216c580 #1191 #1190 #1187 #2220 ; #2606
[assign] (not #2609) justification -1: -381 454 515 516
[decide-and-or] #2449 #2445
[push] 6
[assign] (not #2444) decision axiom
[new-match] 0x56096216c618 #518 #199 #2220 ; #2444 (#196 #196)
[new-match] 0x56096216c648 #203 #199 #2220 ; #2444 (#196 #196)
[new-match] 0x56096216c678 #469 #466 #2219 ; #2444 (#196 #196) (#2220 #2220)
[mk-app] #2613 >= #2405 #337
[mk-app] #2614 not #2613
[mk-app] #2615 I #2405
[mk-app] #2616 has_type #2615 #196
[mk-app] #2617 or #2614 #2616
[mk-app] #2618 not #469
[mk-app] #2619 or #2618 #2614 #2616
[instance] 0x56096216c678 ; 2
[attach-enode] #2615 2
[attach-enode] #2616 2
[end-of-instance]
[assign] (not #2616) justification -1: -455 444
[attach-meaning] #366 arith (- 1)
[mk-app] #2620 * #366 #2405
[mk-app] #2621 + #2219 #2620
[mk-app] #2622 <= #2621 #337
[mk-app] #2623 >= #2621 #337
[attach-enode] #2620 0
[attach-enode] #2621 0
[assign] #2622 justification -1: 444
[assign] #2623 justification -1: 444
[assign] (not #2613) clause -526 527
[resolve-process] true
[resolve-lit] 4 (not #2464)
[resolve-lit] 0 #2613
[resolve-lit] 0 (not #2622)
[resolve-process] #2613
[resolve-lit] 0 #2616
[resolve-process] (not #2622)
[resolve-lit] 4 (not #2406)
[conflict] #2616
[pop] 1 7
[attach-enode] #2615 0
[attach-enode] #2616 0
[assign] #2616 axiom
[assign] #2444 justification -1: 526 444
[new-match] 0x56096216c768 #518 #199 #2220 ; #2444 (#196 #196)
[new-match] 0x56096216c798 #203 #199 #2220 ; #2444 (#196 #196)
[new-match] 0x56096216c7c8 #469 #466 #2219 ; #2444 (#196 #196) (#2220 #2220)
[mk-app] #2620 or #2445 #2613
[mk-app] #2621 or #2567 #2445 #2613
[instance] 0x56096216c768 ; 2
[assign] #2613 justification -1: 70 455
[end-of-instance]
[assign] #2447 clause 456 -455
[attach-meaning] #366 arith (- 1)
[mk-app] #2622 * #366 #2405
[mk-app] #2623 + #2219 #2622
[mk-app] #2618 <= #2623 #337
[mk-app] #2619 >= #2623 #337
[attach-enode] #2622 0
[attach-enode] #2623 0
[assign] #2618 justification -1: 444
[assign] #2619 justification -1: 444
[new-match] 0x560962176858 #1191 #1190 #1213 #2220 ; #2446
[new-match] 0x560962176890 #1209 #1205 #1212 #2220 ; #2446 (#1213 #1213)
[mk-app] #2624 = #2446 #2606
[mk-app] #2625 or #2573 #2624
[instance] 0x560962176858 ; 2
[attach-enode] #2624 2
[attach-meaning] #366 arith (- 1)
[mk-app] #2626 * #366 #2606
[mk-app] #2627 + #2446 #2626
[mk-app] #2628 <= #2627 #337
[mk-app] #2629 >= #2627 #337
[attach-enode] #2626 2
[attach-enode] #2627 2
[assign] #2624 justification -1: 262
[end-of-instance]
[mk-app] #2630 = #2405 #337
[mk-app] #2631 Sub #2405 #292
[mk-app] #2632 nClip #2631
[mk-app] #2633 I #2632
[mk-app] #2634 the_q!model.rec%pow2.? #2633 #1212
[mk-app] #2635 Mul #1196 #2634
[mk-app] #2636 if #2630 #292 #2635
[mk-app] #2637 = #2446 #2636
[mk-app] #2638 or #2445 #2637
[mk-app] #2639 or #2584 #2445 #2637
[instance] 0x560962176890 ; 2
[mk-app] #2640 = #2636 #292
[mk-app] #2641 = #2635 #2636
[attach-enode] #2636 2
[attach-enode] #2630 2
[mk-app] #2642 <= #2405 #337
[attach-enode] #2631 2
[attach-enode] #2632 2
[attach-enode] #2633 2
[attach-enode] #2634 2
[attach-enode] #2635 2
[attach-enode] #2640 2
[attach-enode] #2641 2
[attach-enode] #2637 2
[assign] #2637 justification -1: 263 455
[end-of-instance]
[assign] #2628 clause 531 -530
[assign] #2629 clause 532 -530
[resolve-lit] 1 #2223
[resolve-process] (not #2223)
[resolve-lit] 0 (not #2440)
[resolve-lit] 0 (not #2587)
[resolve-lit] 0 (not #2582)
[resolve-lit] 0 (not #2447)
[resolve-lit] 0 (not #2624)
[resolve-lit] 0 (not #2607)
[resolve-lit] 3 (not #2398)
[resolve-process] (not #2624)
[resolve-process] (not #2447)
[resolve-lit] 0 (not #2444)
[resolve-lit] 4 (not #1221)
[resolve-process] (not #2444)
[resolve-lit] 0 (not #2616)
[resolve-lit] 3 (not #2406)
[resolve-process] (not #2616)
[resolve-process] (not #2607)
[resolve-process] (not #2587)
[resolve-lit] 0 #2575
[resolve-process] #2575
[resolve-lit] 0 #2588
[resolve-process] #2588
[resolve-lit] 0 (not #2565)
[resolve-lit] 3 (not #2462)
[resolve-lit] 3 (not #2485)
[resolve-lit] 3 #2308
[resolve-process] (not #2582)
[resolve-lit] 0 (not #2435)
[resolve-process] (not #2565)
[resolve-process] (not #2440)
[conflict] (not #2435) #2223 (not #1221) #2308
[pop] 1 6
[attach-enode] #2569 0
[attach-enode] #2564 0
[attach-enode] #2561 0
[attach-enode] #2562 0
[assign] #2562 axiom
[attach-enode] #2615 0
[attach-enode] #2616 0
[assign] #2616 axiom
[assign] (not #2435) clause -453 381 -265 373
[resolve-lit] 0 (not #2562)
[resolve-process] #2562
[resolve-lit] 0 #2435
[resolve-lit] 2 (not #2398)
[resolve-process] #2435
[resolve-lit] 0 #2223
[resolve-lit] 3 (not #1221)
[resolve-lit] 2 #2308
[resolve-process] (not #2562)
[conflict] #2223 (not #1221) #2308
[pop] 2 5
[attach-enode] #2569 0
[attach-enode] #2564 0
[attach-enode] #2561 0
[attach-enode] #2562 0
[assign] #2562 axiom
[attach-enode] #2615 0
[attach-enode] #2616 0
[assign] #2616 axiom
[assign] #2223 clause 381 373 -265
[assign] #2213 clause 380 -381 -382
[assign] #2271 clause 384 -380
[assign] (not #2295) clause -393 -384 -394
[assign] #2234 clause 387 393
[assign] #2288 clause 392 393
[assign] #2435 justification -1: 509 443
[assign] #2444 justification -1: 510 444
[attach-meaning] #366 arith (- 1)
[mk-app] #2570 >= #2564 #337
[assign] #2565 justification -1: 443
[assign] #2570 justification -1: 443
[new-match] 0x56096216b490 #570 #564 #2231 #1196 ; #2232
[new-match] 0x56096216b4c8 #1865 #564 #2231 #1196 ; #2232
[new-match] 0x56096216b500 #1221 #1217 #2228 ; #2229
[mk-app] #2586 * #2231 #1196
[mk-app] #2587 * #366 #2586
[mk-app] #2596 + #2232 #2587
[mk-app] #2597 = #2596 #337
[mk-app] #2598 * #1196 #2231
[inst-discovered] theory-solving 0 arith# ; #2586
[mk-app] #2599 = #2586 #2598
[instance] 0 #2599
[attach-enode] #2599 0
[end-of-instance]
[mk-app] #2599 Int
[attach-meaning] #2599 arith (- 2)
[mk-app] #2595 * #2599 #2231
[mk-app] #2593 * #366 #2598
[inst-discovered] theory-solving 0 arith# ; #2593
[mk-app] #2609 = #2593 #2595
[instance] 0 #2609
[attach-enode] #2609 0
[end-of-instance]
[mk-app] #2598 + #2595 #2232
[mk-app] #2593 + #2232 #2595
[inst-discovered] theory-solving 0 arith# ; #2593
[mk-app] #2609 = #2593 #2598
[instance] 0 #2609
[attach-enode] #2609 0
[end-of-instance]
[mk-app] #2593 * #1196 #2231
[attach-meaning] #366 arith (- 1)
[mk-app] #2609 * #366 #2232
[mk-app] #2610 + #2593 #2609
[mk-app] #2611 = #2610 #337
[mk-app] #2612 = #2598 #337
[inst-discovered] theory-solving 0 arith# ; #2612
[mk-app] #2622 = #2612 #2611
[instance] 0 #2622
[attach-enode] #2622 0
[end-of-instance]
[mk-app] #2599 or #2422 #2611
[instance] 0x56096216b490 ; 1
[attach-enode] #2593 1
[attach-enode] #2609 1
[attach-enode] #2610 1
[attach-enode] #2611 1
[mk-app] #2595 <= #2610 #337
[mk-app] #2598 >= #2610 #337
[assign] #2611 justification -1: 78
[end-of-instance]
[mk-app] #2612 >= #2232 #337
[mk-app] #2622 or #2430 #2509 #2612
[mk-app] #2623 or #2509 #2612
[mk-app] #2618 or #2 #2509 #2612
[inst-discovered] theory-solving 0 basic# ; #2618
[mk-app] #2619 = #2618 #2623
[instance] 0 #2619
[attach-enode] #2619 0
[end-of-instance]
[mk-app] #2618 or #2436 #2509 #2612
[instance] 0x56096216b4c8 ; 1
[end-of-instance]
[mk-app] #2623 has_type #2228 #196
[mk-app] #2619 not #2623
[mk-app] #2626 the_q!model.rec%pow2.? #2228 #1213
[mk-app] #2627 = #2229 #2626
[mk-app] #2628 or #2619 #2627
[mk-app] #2629 or #2442 #2619 #2627
[instance] 0x56096216b500 ; 1
[attach-enode] #2623 1
[attach-enode] #2626 1
[attach-enode] #2627 1
[end-of-instance]
[assign] #2440 clause 454 -453
[assign] #2447 clause 456 -455
[assign] (not #2588) clause -508 -507 -460 -472 373 -369
[assign] #2595 clause 513 -512
[assign] #2598 clause 514 -512
[new-match] 0x56096216bb08 #1191 #1190 #1213 #2216 ; #2439
[new-match] 0x56096216bb40 #1209 #1205 #1212 #2216 ; #2439 (#1213 #1213)
[new-match] 0x56096216bb78 #1191 #1190 #1213 #2220 ; #2446
[new-match] 0x56096216bbb0 #1209 #1205 #1212 #2220 ; #2446 (#1213 #1213)
[mk-app] #2642 not #1191
[mk-app] #2640 or #2642 #2572
[instance] 0x56096216bb08 ; 2
[attach-enode] #1187 2
[attach-enode] #2571 2
[attach-enode] #2572 2
[assign] #2572 justification -1: 262
[end-of-instance]
[mk-app] #2641 not #1209
[mk-app] #2584 or #2641 #2438 #2582
[instance] 0x56096216bb40 ; 2
[mk-app] #2639 = #2581 #292
[mk-app] #2573 = #2580 #2581
[attach-enode] #2581 2
[attach-enode] #2575 2
[assign] #2559 justification -1: -508
[assign] (not #2575) justification -1: -508
[attach-enode] #2576 2
[attach-enode] #2577 2
[attach-enode] #2578 2
[attach-enode] #2579 2
[attach-enode] #2580 2
[attach-enode] #2639 2
[attach-enode] #2573 2
[assign] #2573 justification -1: -519
[attach-enode] #2582 2
[assign] #2582 justification -1: 263 453
[end-of-instance]
[mk-app] #2625 or #2642 #2624
[instance] 0x56096216bb78 ; 2
[attach-enode] #2606 2
[attach-enode] #2624 2
[assign] #2624 justification -1: 262
[end-of-instance]
[mk-app] #2567 or #2641 #2445 #2637
[instance] 0x56096216bbb0 ; 2
[mk-app] #2621 = #2636 #292
[mk-app] #2608 = #2635 #2636
[attach-enode] #2636 2
[attach-enode] #2630 2
[mk-app] #2605 <= #2405 #337
[attach-enode] #2631 2
[attach-enode] #2632 2
[attach-enode] #2633 2
[attach-enode] #2634 2
[attach-enode] #2635 2
[attach-enode] #2621 2
[attach-enode] #2608 2
[attach-enode] #2637 2
[assign] #2637 justification -1: 263 455
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2594 * #366 #2405
[mk-app] #2585 + #2219 #2594
[mk-app] #2574 <= #2585 #337
[mk-app] #2568 >= #2585 #337
[attach-enode] #2594 0
[attach-enode] #2585 0
[assign] #2574 justification -1: 444
[assign] #2568 justification -1: 444
[eq-expl] #1187 root
[new-match] 0x560962176c18 #1191 #1190 #1187 #2216 ; #2571
[eq-expl] #2576 cg (#2387 #2215) (#292 #292) ; #2218
[eq-expl] #2577 cg (#2576 #2218) ; #2219
[eq-expl] #2578 cg (#2577 #2219) ; #2220
[new-match] 0x560962176c50 #1191 #1190 #1212 #2578 ; #2579
[new-match] 0x560962176c88 #1191 #1190 #1187 #2220 ; #2606
[eq-expl] #2579 root
[new-match] 0x560962176cc0 #570 #564 #2579 #1196 ; #2580
[new-match] 0x560962176cf8 #1865 #564 #2579 #1196 ; #2580
[mk-app] #2643 or #2642 #2607
[instance] 0x560962176c50 ; 3
[attach-enode] #2604 3
[attach-enode] #2607 3
[assign] #2607 justification -1: 262
[end-of-instance]
[mk-app] #2644 * #1196 #2579
[inst-discovered] theory-solving 0 arith# ; #2589
[mk-app] #2645 = #2589 #2644
[instance] 0 #2645
[attach-enode] #2645 0
[end-of-instance]
[mk-app] #2645 Int
[attach-meaning] #2645 arith (- 2)
[mk-app] #2646 * #2645 #2579
[mk-app] #2647 * #366 #2644
[inst-discovered] theory-solving 0 arith# ; #2647
[mk-app] #2648 = #2647 #2646
[instance] 0 #2648
[attach-enode] #2648 0
[end-of-instance]
[mk-app] #2644 + #2646 #2580
[mk-app] #2647 + #2580 #2646
[inst-discovered] theory-solving 0 arith# ; #2647
[mk-app] #2648 = #2647 #2644
[instance] 0 #2648
[attach-enode] #2648 0
[end-of-instance]
[mk-app] #2647 * #1196 #2579
[attach-meaning] #366 arith (- 1)
[mk-app] #2648 * #366 #2580
[mk-app] #2649 + #2647 #2648
[mk-app] #2650 = #2649 #337
[mk-app] #2651 = #2644 #337
[inst-discovered] theory-solving 0 arith# ; #2651
[mk-app] #2652 = #2651 #2650
[instance] 0 #2652
[attach-enode] #2652 0
[end-of-instance]
[mk-app] #2645 or #2422 #2650
[instance] 0x560962176cc0 ; 3
[attach-enode] #2647 3
[attach-enode] #2648 3
[attach-enode] #2649 3
[attach-enode] #2650 3
[mk-app] #2646 <= #2649 #337
[mk-app] #2644 >= #2649 #337
[assign] #2650 justification -1: 78
[end-of-instance]
[mk-app] #2651 or #2601 #2602
[mk-app] #2652 or #2 #2601 #2602
[inst-discovered] theory-solving 0 basic# ; #2652
[mk-app] #2653 = #2652 #2651
[instance] 0 #2653
[attach-enode] #2653 0
[end-of-instance]
[mk-app] #2652 or #2436 #2601 #2602
[instance] 0x560962176cf8 ; 3
[end-of-instance]
[assign] #2646 clause 535 -534
[assign] #2644 clause 536 -534
[mk-app] #2651 = #2222 #2580
[attach-meaning] #366 arith (- 1)
[mk-app] #2653 + #2222 #2648
[mk-app] #2654 <= #2653 #337
[mk-app] #2655 >= #2653 #337
[assign] #2651 justification -1: 522 523 454 381
[attach-enode] #2651 0
[attach-enode] #2653 0
[assign] #2654 justification -1: 539
[assign] #2655 justification -1: 539
[mk-app] #2656 = #2221 #2579
[attach-meaning] #366 arith (- 1)
[mk-app] #2657 * #366 #2579
[mk-app] #2658 + #2221 #2657
[mk-app] #2659 <= #2658 #337
[mk-app] #2660 >= #2658 #337
[assign] #2656 justification -1: 456 533 524 443
[attach-enode] #2656 0
[attach-enode] #2657 0
[attach-enode] #2658 0
[assign] #2659 justification -1: 542
[assign] #2660 justification -1: 542
[assign] #2613 clause 527 -464 -531
[decide-and-or] #2324 #2200
[push] 3
[assign] #2200 decision axiom
[assign] #2277 clause 391 -374
[assign] (not #2273) clause -389 -391 -392
[assign] #2235 clause 388 389
[assign] (not #2227) clause -385 389
[assign] (not #2233) clause -386 385 -387
[decide-and-or] #2437 #2432
[push] 4
[assign] (not #2431) decision axiom
[assign] (not #2433) clause -452 451 -450
[assign] (not #2602) clause -538 451 -450 -541
[assign] (not #2600) clause -537 451 -535 -450 -541
[decide-and-or] #2512 #2507
[push] 5
[assign] (not #2506) decision axiom
[decide-and-or] #2518 #2514
[push] 6
[assign] (not #2513) decision axiom
[new-match] 0x560962177898 #518 #199 #2411 ; #2513 (#196 #196)
[new-match] 0x5609621778c8 #203 #199 #2411 ; #2513 (#196 #196)
[eq-expl] #2410 lit #2532 ; #2531
[eq-expl] #2531 root
[new-match] 0x5609621778f8 #469 #466 #2410 ; #2513 (#196 #196) (#2411 #2411)
[mk-app] #2661 >= #2531 #337
[mk-app] #2662 not #2661
[mk-app] #2663 I #2531
[mk-app] #2664 has_type #2663 #196
[mk-app] #2665 or #2662 #2664
[mk-app] #2666 not #469
[mk-app] #2667 or #2666 #2662 #2664
[instance] 0x5609621778f8 ; 3
[attach-enode] #2663 3
[attach-enode] #2664 3
[end-of-instance]
[assign] (not #2664) justification -1: -489 495
[attach-meaning] #366 arith (- 1)
[mk-app] #2668 * #366 #2531
[mk-app] #2669 + #2410 #2668
[mk-app] #2670 <= #2669 #337
[mk-app] #2671 >= #2669 #337
[attach-enode] #2668 0
[attach-enode] #2669 0
[assign] #2670 justification -1: 495
[assign] #2671 justification -1: 495
[assign] (not #2661) clause -545 546
[resolve-process] true
[resolve-lit] 4 (not #2537)
[resolve-lit] 0 #2661
[resolve-lit] 0 (not #2670)
[resolve-process] #2661
[resolve-lit] 0 #2664
[resolve-process] (not #2670)
[resolve-lit] 4 (not #2532)
[conflict] #2664
[pop] 1 7
[attach-enode] #2663 0
[attach-enode] #2664 0
[assign] #2664 axiom
[assign] #2513 justification -1: 545 495
[new-match] 0x5609621779e8 #518 #199 #2411 ; #2513 (#196 #196)
[new-match] 0x560962177a18 #203 #199 #2411 ; #2513 (#196 #196)
[new-match] 0x560962177a48 #469 #466 #2410 ; #2513 (#196 #196) (#2411 #2411)
[mk-app] #2668 or #2514 #2661
[mk-app] #2669 not #518
[mk-app] #2670 or #2669 #2514 #2661
[instance] 0x5609621779e8 ; 3
[assign] #2661 justification -1: 70 489
[end-of-instance]
[assign] #2516 clause 490 -489
[attach-meaning] #366 arith (- 1)
[mk-app] #2671 * #366 #2531
[mk-app] #2666 + #2410 #2671
[mk-app] #2667 <= #2666 #337
[mk-app] #2672 >= #2666 #337
[attach-enode] #2671 0
[attach-enode] #2666 0
[assign] #2667 justification -1: 495
[assign] #2672 justification -1: 495
[new-match] 0x560962177cc0 #1191 #1190 #1213 #2411 ; #2515
[new-match] 0x560962177cf8 #1209 #1205 #1212 #2411 ; #2515 (#1213 #1213)
[mk-app] #2673 the_q!model.rec%pow2.? #2411 #1187
[mk-app] #2674 = #2515 #2673
[mk-app] #2675 or #2642 #2674
[instance] 0x560962177cc0 ; 3
[attach-enode] #2673 3
[attach-enode] #2674 3
[assign] #2674 justification -1: 262
[end-of-instance]
[mk-app] #2676 = #2531 #337
[mk-app] #2677 Sub #2531 #292
[mk-app] #2678 nClip #2677
[mk-app] #2679 I #2678
[mk-app] #2680 the_q!model.rec%pow2.? #2679 #1212
[mk-app] #2681 Mul #1196 #2680
[mk-app] #2682 if #2676 #292 #2681
[mk-app] #2683 = #2515 #2682
[mk-app] #2684 or #2514 #2683
[mk-app] #2685 or #2641 #2514 #2683
[instance] 0x560962177cf8 ; 3
[mk-app] #2686 = #2682 #292
[mk-app] #2687 = #2681 #2682
[attach-enode] #2682 3
[attach-enode] #2676 3
[mk-app] #2688 <= #2531 #337
[attach-enode] #2677 3
[attach-enode] #2678 3
[attach-enode] #2679 3
[attach-enode] #2680 3
[attach-enode] #2681 3
[attach-enode] #2686 3
[attach-enode] #2687 3
[attach-enode] #2683 3
[assign] #2683 justification -1: 263 489
[end-of-instance]
[new-match] 0x560962178500 #1191 #1190 #1187 #2411 ; #2673
[decide-and-or] #2524 #2520
[push] 6
[assign] (not #2519) decision axiom
[new-match] 0x560962178578 #518 #199 #2230 ; #2519 (#196 #196)
[new-match] 0x5609621785a8 #203 #199 #2230 ; #2519 (#196 #196)
[new-match] 0x5609621785d8 #469 #466 #2205 ; #2519 (#196 #196) (#2230 #2230)
[mk-app] #2689 or #2347 #2519
[mk-app] #2690 not #469
[mk-app] #2691 or #2690 #2347 #2519
[instance] 0x5609621785d8 ; 2
[end-of-instance]
[resolve-process] true
[resolve-lit] 4 (not #2346)
[resolve-lit] 0 #2519
[conflict] #2519
[pop] 1 7
[assign] #2519 axiom
[assign] #2522 clause 492 -491
[new-match] 0x560962178588 #518 #199 #2230 ; #2519 (#196 #196)
[new-match] 0x5609621785b8 #203 #199 #2230 ; #2519 (#196 #196)
[new-match] 0x5609621785e8 #469 #466 #2205 ; #2519 (#196 #196) (#2230 #2230)
[new-match] 0x560962178618 #1191 #1190 #1213 #2230 ; #2521
[new-match] 0x560962178650 #1209 #1205 #1212 #2230 ; #2521 (#1213 #1213)
[mk-app] #2690 >= #2389 #337
[mk-app] #2691 or #2520 #2690
[mk-app] #2692 or #2669 #2520 #2690
[instance] 0x560962178588 ; 2
[assign] #2690 justification -1: 70 491
[end-of-instance]
[mk-app] #2693 the_q!model.rec%pow2.? #2230 #1187
[mk-app] #2694 = #2521 #2693
[mk-app] #2695 or #2642 #2694
[instance] 0x560962178618 ; 2
[attach-enode] #2693 2
[attach-enode] #2694 2
[assign] #2694 justification -1: 262
[end-of-instance]
[mk-app] #2696 = #2389 #337
[mk-app] #2697 Sub #2389 #292
[mk-app] #2698 nClip #2697
[mk-app] #2699 I #2698
[mk-app] #2700 the_q!model.rec%pow2.? #2699 #1212
[mk-app] #2701 Mul #1196 #2700
[mk-app] #2702 if #2696 #292 #2701
[mk-app] #2703 = #2521 #2702
[mk-app] #2704 or #2520 #2703
[mk-app] #2705 or #2641 #2520 #2703
[instance] 0x560962178650 ; 2
[mk-app] #2706 = #2702 #292
[mk-app] #2707 = #2701 #2702
[attach-enode] #2702 2
[attach-enode] #2696 2
[mk-app] #2708 <= #2389 #337
[attach-enode] #2697 2
[attach-enode] #2698 2
[attach-enode] #2699 2
[attach-enode] #2700 2
[attach-enode] #2701 2
[attach-enode] #2706 2
[attach-enode] #2707 2
[attach-enode] #2703 2
[assign] #2703 justification -1: 263 491
[end-of-instance]
[attach-meaning] #366 arith (- 1)
[mk-app] #2709 * #366 #2389
[mk-app] #2710 + #2205 #2709
[mk-app] #2711 <= #2710 #337
[mk-app] #2712 >= #2710 #337
[attach-enode] #2709 0
[attach-enode] #2710 0
[assign] #2711 justification -1: 442
[assign] #2712 justification -1: 442
[new-match] 0x56096217d580 #1191 #1190 #1187 #2230 ; #2693
[decide-and-or] #2530 #2526
[push] 6
[assign] (not #2525) decision axiom
[new-match] 0x56096217d648 #518 #199 #2239 ; #2525 (#196 #196)
[new-match] 0x56096217d678 #203 #199 #2239 ; #2525 (#196 #196)
[eq-expl] #2191 lit #2535 ; #2534
[eq-expl] #2534 root
[new-match] 0x56096217d6a8 #469 #466 #2191 ; #2525 (#196 #196) (#2239 #2239)
[mk-app] #2713 >= #2534 #337
[mk-app] #2714 not #2713
[mk-app] #2715 I #2534
[mk-app] #2716 has_type #2715 #196
[mk-app] #2717 or #2714 #2716
[mk-app] #2718 not #469
[mk-app] #2719 or #2718 #2714 #2716
[instance] 0x56096217d6a8 ; 2
[attach-enode] #2715 2
[attach-enode] #2716 2
[end-of-instance]
[assign] (not #2716) justification -1: -493 496
[attach-meaning] #366 arith (- 1)
[mk-app] #2720 * #366 #2534
[mk-app] #2721 + #2191 #2720
[mk-app] #2722 <= #2721 #337
[mk-app] #2723 >= #2721 #337
[attach-enode] #2720 0
[attach-enode] #2721 0
[assign] #2722 justification -1: 496
[assign] #2723 justification -1: 496
[assign] (not #2713) clause -564 565
[resolve-process] true
[resolve-lit] 0 #2713
[resolve-lit] 0 (not #2722)
[resolve-process] #2713
[resolve-lit] 0 #2716
[resolve-process] (not #2722)
[resolve-lit] 4 (not #2535)
[conflict] #2716
[pop] 1 7
[attach-enode] #2715 0
[attach-enode] #2716 0
[assign] #2716 axiom
[assign] #2525 justification -1: 564 496
[new-match] 0x56096217d798 #518 #199 #2239 ; #2525 (#196 #196)
[new-match] 0x56096217d7c8 #203 #199 #2239 ; #2525 (#196 #196)
[new-match] 0x56096217d7f8 #469 #466 #2191 ; #2525 (#196 #196) (#2239 #2239)
[mk-app] #2720 or #2526 #2713
[mk-app] #2721 or #2669 #2526 #2713
[instance] 0x56096217d798 ; 2
[assign] #2713 justification -1: 70 493
[end-of-instance]
[assign] #2528 clause 494 -493
[attach-meaning] #366 arith (- 1)
[mk-app] #2722 * #366 #2534
[mk-app] #2723 + #2191 #2722
[mk-app] #2718 <= #2723 #337
[mk-app] #2719 >= #2723 #337
[attach-enode] #2722 0
[attach-enode] #2723 0
[assign] #2718 justification -1: 496
[assign] #2719 justification -1: 496
[new-match] 0x56096217da70 #1191 #1190 #1213 #2239 ; #2527
[new-match] 0x56096217daa8 #1209 #1205 #1212 #2239 ; #2527 (#1213 #1213)
[mk-app] #2724 the_q!model.rec%pow2.? #2239 #1187
[mk-app] #2725 = #2527 #2724
[mk-app] #2726 or #2642 #2725
[instance] 0x56096217da70 ; 2
[attach-enode] #2724 2
[attach-enode] #2725 2
[assign] #2725 justification -1: 262
[end-of-instance]
[mk-app] #2727 = #2534 #337
[mk-app] #2728 Sub #2534 #292
[mk-app] #2729 nClip #2728
[mk-app] #2730 I #2729
[mk-app] #2731 the_q!model.rec%pow2.? #2730 #1212
[mk-app] #2732 Mul #1196 #2731
[mk-app] #2733 if #2727 #292 #2732
[mk-app] #2734 = #2527 #2733
[mk-app] #2735 or #2526 #2734
[mk-app] #2736 or #2641 #2526 #2734
[instance] 0x56096217daa8 ; 2
[mk-app] #2737 = #2733 #292
[mk-app] #2738 = #2732 #2733
[attach-enode] #2733 2
[attach-enode] #2727 2
[mk-app] #2739 <= #2534 #337
[attach-enode] #2728 2
[attach-enode] #2729 2
[attach-enode] #2730 2
[attach-enode] #2731 2
[attach-enode] #2732 2
[attach-enode] #2737 2
[attach-enode] #2738 2
[attach-enode] #2734 2
[assign] #2734 justification -1: 263 493
[end-of-instance]
[new-match] 0x56096217e2b0 #1191 #1190 #1187 #2239 ; #2724
[decide-and-or] #2618 #2509
[push] 6
[assign] (not #2508) decision axiom
[assign] (not #2612) clause -515 487 -514
[decide-and-or] #2629 #2619
[push] 7
[assign] (not #2623) decision axiom
[new-match] 0x56096217e340 #518 #199 #2228 ; #2623 (#196 #196)
[new-match] 0x56096217e370 #203 #199 #2228 ; #2623 (#196 #196)
[new-match] 0x56096217e3a0 #469 #466 #2193 ; #2623 (#196 #196) (#2228 #2228)
[mk-app] #2740 not #2197
[mk-app] #2741 or #2740 #2623
[mk-app] #2742 not #469
[mk-app] #2743 or #2742 #2740 #2623
[instance] 0x56096217e3a0 ; 2
[end-of-instance]
[resolve-process] true
[resolve-lit] 0 #2623
[conflict] #2623
[pop] 1 8
[assign] #2623 axiom
[assign] #2627 clause 517 -516
[new-match] 0x56096217e350 #518 #199 #2228 ; #2623 (#196 #196)
[new-match] 0x56096217e380 #203 #199 #2228 ; #2623 (#196 #196)
[new-match] 0x56096217e3b0 #469 #466 #2193 ; #2623 (#196 #196) (#2228 #2228)
[new-match] 0x56096217e3e0 #1191 #1190 #1213 #2228 ; #2626
[new-match] 0x56096217e418 #1209 #1205 #1212 #2228 ; #2626 (#1213 #1213)
[mk-app] #2742 >= #2385 #337
[mk-app] #2743 or #2619 #2742
[mk-app] #2744 or #2669 #2619 #2742
[instance] 0x56096217e350 ; 2
[assign] #2742 justification -1: 70 516
[end-of-instance]
[mk-app] #2745 the_q!model.rec%pow2.? #2228 #1187
[mk-app] #2746 = #2626 #2745
[mk-app] #2747 or #2642 #2746
[instance] 0x56096217e3e0 ; 2
[attach-enode] #2745 2
[attach-enode] #2746 2
[assign] #2746 justification -1: 262
[end-of-instance]
[mk-app] #2748 = #2385 #337
[mk-app] #2749 Sub #2385 #292
[mk-app] #2750 nClip #2749
[mk-app] #2751 I #2750
[mk-app] #2752 the_q!model.rec%pow2.? #2751 #1212
[mk-app] #2753 Mul #1196 #2752
[mk-app] #2754 if #2748 #292 #2753
[mk-app] #2755 = #2626 #2754
[mk-app] #2756 or #2619 #2755
[mk-app] #2757 or #2641 #2619 #2755
[instance] 0x56096217e418 ; 2
[mk-app] #2758 = #2754 #292
[mk-app] #2759 = #2753 #2754
[attach-enode] #2754 2
[attach-enode] #2748 2
[mk-app] #2760 <= #2385 #337
[attach-enode] #2749 2
[attach-enode] #2750 2
[attach-enode] #2751 2
[attach-enode] #2752 2
[attach-enode] #2753 2
[attach-enode] #2758 2
[attach-enode] #2759 2
[attach-enode] #2755 2
[assign] #2755 justification -1: 263 516
[end-of-instance]
[assign] (not #2748) justification -1: -372 441
[attach-meaning] #366 arith (- 1)
[mk-app] #2761 * #366 #2385
[mk-app] #2762 + #2193 #2761
[mk-app] #2763 <= #2762 #337
[mk-app] #2764 >= #2762 #337
[attach-enode] #2761 0
[attach-enode] #2762 0
[assign] #2763 justification -1: 441
[assign] #2764 justification -1: 441
[new-match] 0x56096211ea90 #1191 #1190 #1187 #2228 ; #2745
[assign] (not #2760) clause -577 576
[assign] #2759 clause 579 576
[eq-expl] #2752 root
[new-match] 0x56096211eb40 #570 #564 #2752 #1196 ; #2753
[new-match] 0x56096211eb78 #1865 #564 #2752 #1196 ; #2753
[eq-expl] #2385 lit #2386 ; #2193
[eq-expl] #2749 cg (#2385 #2193) (#292 #292) ; #2204
[eq-expl] #2204 lit #2350 ; #2205
[eq-expl] #2750 cg (#2749 #2204) ; #2205
[eq-expl] #2751 cg (#2750 #2205) ; #2230
[new-match] 0x56096211ebb0 #1191 #1190 #1212 #2751 ; #2752
[mk-app] #2765 * #2752 #1196
[mk-app] #2766 * #366 #2765
[mk-app] #2767 + #2753 #2766
[mk-app] #2768 = #2767 #337
[mk-app] #2769 * #1196 #2752
[inst-discovered] theory-solving 0 arith# ; #2765
[mk-app] #2770 = #2765 #2769
[instance] 0 #2770
[attach-enode] #2770 0
[end-of-instance]
[mk-app] #2770 Int
[attach-meaning] #2770 arith (- 2)
[mk-app] #2771 * #2770 #2752
[mk-app] #2772 * #366 #2769
[inst-discovered] theory-solving 0 arith# ; #2772
[mk-app] #2773 = #2772 #2771
[instance] 0 #2773
[attach-enode] #2773 0
[end-of-instance]
[mk-app] #2769 + #2771 #2753
[mk-app] #2772 + #2753 #2771
[inst-discovered] theory-solving 0 arith# ; #2772
[mk-app] #2773 = #2772 #2769
[instance] 0 #2773
[attach-enode] #2773 0
[end-of-instance]
[mk-app] #2772 * #1196 #2752
[attach-meaning] #366 arith (- 1)
[mk-app] #2773 * #366 #2753
[mk-app] #2774 + #2772 #2773
[mk-app] #2775 = #2774 #337
[mk-app] #2776 = #2769 #337
[inst-discovered] theory-solving 0 arith# ; #2776
[mk-app] #2777 = #2776 #2775
[instance] 0 #2777
[attach-enode] #2777 0
[end-of-instance]
[mk-app] #2770 or #2422 #2775
[instance] 0x56096211eb40 ; 3
[attach-enode] #2772 3
[attach-enode] #2773 3
[attach-enode] #2774 3
[attach-enode] #2775 3
[mk-app] #2771 <= #2774 #337
[mk-app] #2769 >= #2774 #337
[assign] #2775 justification -1: 78
[end-of-instance]
[mk-app] #2776 >= #2752 #337
[mk-app] #2777 not #2776
[mk-app] #2778 >= #2753 #337
[mk-app] #2779 or #2430 #2777 #2778
[mk-app] #2780 or #2777 #2778
[mk-app] #2781 or #2 #2777 #2778
[inst-discovered] theory-solving 0 basic# ; #2781
[mk-app] #2782 = #2781 #2780
[instance] 0 #2782
[attach-enode] #2782 0
[end-of-instance]
[mk-app] #2781 or #2436 #2777 #2778
[instance] 0x56096211eb78 ; 3
[end-of-instance]
[mk-app] #2780 the_q!model.rec%pow2.? #2230 #1212
[mk-app] #2782 = #2780 #2693
[mk-app] #2783 or #2642 #2782
[instance] 0x56096211ebb0 ; 3
[attach-enode] #2780 3
[attach-enode] #2782 3
[assign] #2782 justification -1: 262
[end-of-instance]
[assign] #2771 clause 584 -583
[assign] #2769 clause 585 -583
[resolve-lit] 3 #2233
[resolve-process] (not #2233)
[resolve-lit] 0 (not #2627)
[resolve-lit] 0 (not #2759)
[resolve-lit] 0 (not #2755)
[resolve-lit] 1 (not #2522)
[resolve-lit] 0 (not #2782)
[resolve-lit] 1 (not #2694)
[resolve-lit] 4 (not #2386)
[resolve-process] (not #2782)
[resolve-process] (not #2759)
[resolve-lit] 0 #2748
[resolve-process] #2748
[resolve-lit] 4 #2199
[resolve-process] (not #2755)
[resolve-lit] 0 (not #2623)
[resolve-process] (not #2627)
[resolve-lit] 5 (not #1221)
[conflict] (not #2623) #2233 (not #2522) #2199 (not #1221)
[pop] 1 7
[assign] #2623 axiom
[resolve-process] true
[resolve-lit] 0 (not #2623)
[resolve-lit] 0 (not #2522)
[resolve-lit] 2 #2233
[resolve-lit] 3 #2199
[resolve-lit] 4 (not #1221)
[resolve-process] (not #2623)
[conflict] (not #2522) #2233 #2199 (not #1221)
[pop] 2 6
[attach-enode] #2663 0
[attach-enode] #2664 0
[assign] #2664 axiom
[assign] #2519 axiom
[attach-enode] #2715 0
[attach-enode] #2716 0
[assign] #2716 axiom
[assign] #2623 axiom
[assign] (not #2522) clause -492 386 372 -265
[resolve-process] true
[resolve-lit] 0 #2522
[resolve-lit] 0 (not #2519)
[resolve-lit] 2 (not #1221)
[resolve-process] #2522
[resolve-lit] 0 #2233
[resolve-lit] 1 #2199
[resolve-process] (not #2519)
[conflict] #2233 (not #1221) #2199
[pop] 1 4
[attach-enode] #2663 0
[attach-enode] #2664 0
[assign] #2664 axiom
[assign] #2519 axiom
[attach-enode] #2715 0
[attach-enode] #2716 0
[assign] #2716 axiom
[assign] #2623 axiom
[assign] #2233 clause 386 372 -265
[assign] #2522 clause 492 -491
[assign] #2627 clause 517 -516
[assign] #2227 clause 385 -386 -387
[assign] #2273 clause 389 -385
[assign] (not #2277) clause -391 -389 -392
[assign] #2244 clause 390 391
[assign] (not #2200) clause -374 391
[assign] #2259 clause 397 374
[assign] (not #2261) clause -398 374
[assign] #2513 justification -1: 545 495
[assign] #2525 justification -1: 546 496
[new-match] 0x560962177bd0 #1191 #1190 #1213 #2230 ; #2521
[new-match] 0x560962177c08 #1209 #1205 #1212 #2230 ; #2521 (#1213 #1213)
[new-match] 0x560962177c40 #1191 #1190 #1213 #2228 ; #2626
[new-match] 0x560962177c78 #1209 #1205 #1212 #2228 ; #2626 (#1213 #1213)
[eq-expl] #2240 root
[eq-expl] #2232 root
[new-match] 0x560962177cb0 #570 #564 #2232 #2240 ; #2243
[new-match] 0x560962177ce8 #1865 #564 #2232 #2240 ; #2243
[eq-expl] #2241 root
[new-match] 0x560962177d20 #570 #564 #2241 #1196 ; #2242
[new-match] 0x560962177d58 #1865 #564 #2241 #1196 ; #2242
[mk-app] #2671 or #2642 #2694
[instance] 0x560962177bd0 ; 2
[attach-enode] #2693 2
[attach-enode] #2694 2
[assign] #2694 justification -1: 262
[end-of-instance]
[mk-app] #2666 or #2641 #2520 #2703
[instance] 0x560962177c08 ; 2
[mk-app] #2667 = #2702 #292
[mk-app] #2672 = #2701 #2702
[attach-enode] #2702 2
[attach-enode] #2696 2
[attach-enode] #2697 2
[attach-enode] #2698 2
[attach-enode] #2699 2
[attach-enode] #2700 2
[attach-enode] #2701 2
[attach-enode] #2667 2
[attach-enode] #2672 2
[attach-enode] #2703 2
[assign] #2703 justification -1: 263 491
[end-of-instance]
[mk-app] #2688 or #2642 #2746
[instance] 0x560962177c40 ; 2
[attach-enode] #2745 2
[attach-enode] #2746 2
[assign] #2746 justification -1: 262
[end-of-instance]
[mk-app] #2686 or #2641 #2619 #2755
[instance] 0x560962177c78 ; 2
[mk-app] #2687 = #2754 #292
[mk-app] #2708 = #2753 #2754
[attach-enode] #2754 2
[attach-enode] #2748 2
[attach-enode] #2749 2
[attach-enode] #2750 2
[attach-enode] #2751 2
[attach-enode] #2752 2
[attach-enode] #2753 2
[attach-enode] #2687 2
[attach-enode] #2708 2
[attach-enode] #2755 2
[assign] #2755 justification -1: 263 516
[end-of-instance]
[mk-app] #2706 * #2232 #2240
[mk-app] #2707 * #366 #2706
[mk-app] #2709 + #2243 #2707
[mk-app] #2710 = #2709 #337
[mk-app] #2711 or #2422 #2710
[instance] 0x560962177cb0 ; 1
[attach-enode] #2706 1
[attach-enode] #2707 1
[attach-enode] #2709 1
[attach-enode] #2710 1
[mk-app] #2712 <= #2709 #337
[mk-app] #2722 >= #2709 #337
[assign] #2710 justification -1: 78
[end-of-instance]
[mk-app] #2723 not #2612
[mk-app] #2718 >= #2243 #337
[mk-app] #2719 or #2507 #2723 #2718
[mk-app] #2739 or #2436 #2507 #2723 #2718
[instance] 0x560962177ce8 ; 1
[end-of-instance]
[mk-app] #2737 * #2241 #1196
[mk-app] #2738 * #366 #2737
[mk-app] #2736 + #2242 #2738
[mk-app] #2726 = #2736 #337
[mk-app] #2669 * #1196 #2241
[inst-discovered] theory-solving 0 arith# ; #2737
[mk-app] #2721 = #2737 #2669
[instance] 0 #2721
[attach-enode] #2721 0
[end-of-instance]
[mk-app] #2721 Int
[attach-meaning] #2721 arith (- 2)
[mk-app] #2705 * #2721 #2241
[mk-app] #2695 * #366 #2669
[inst-discovered] theory-solving 0 arith# ; #2695
[mk-app] #2692 = #2695 #2705
[instance] 0 #2692
[attach-enode] #2692 0
[end-of-instance]
[mk-app] #2669 + #2705 #2242
[mk-app] #2695 + #2242 #2705
[inst-discovered] theory-solving 0 arith# ; #2695
[mk-app] #2692 = #2695 #2669
[instance] 0 #2692
[attach-enode] #2692 0
[end-of-instance]
[mk-app] #2695 * #1196 #2241
[attach-meaning] #366 arith (- 1)
[mk-app] #2692 * #366 #2242
[mk-app] #2685 + #2695 #2692
[mk-app] #2675 = #2685 #337
[mk-app] #2670 = #2669 #337
[inst-discovered] theory-solving 0 arith# ; #2670
[mk-app] #2760 = #2670 #2675
[instance] 0 #2760
[attach-enode] #2760 0
[end-of-instance]
[mk-app] #2721 or #2422 #2675
[instance] 0x560962177d20 ; 1
[attach-enode] #2695 1
[attach-enode] #2692 1
[attach-enode] #2685 1
[attach-enode] #2675 1
[mk-app] #2705 <= #2685 #337
[mk-app] #2669 >= #2685 #337
[assign] #2675 justification -1: 78
[end-of-instance]
[mk-app] #2670 not #2510
[mk-app] #2760 >= #2242 #337
[mk-app] #2758 or #2430 #2670 #2760
[mk-app] #2759 or #2670 #2760
[mk-app] #2761 or #2 #2670 #2760
[inst-discovered] theory-solving 0 basic# ; #2761
[mk-app] #2762 = #2761 #2759
[instance] 0 #2762
[attach-enode] #2762 0
[end-of-instance]
[mk-app] #2761 or #2436 #2670 #2760
[instance] 0x560962177d58 ; 1
[end-of-instance]
[assign] #2516 clause 490 -489
[assign] #2528 clause 494 -493
[assign] #2712 clause 558 -557
[assign] #2722 clause 559 -557
[assign] #2705 clause 562 -561
[assign] #2669 clause 563 -561
[assign] (not #2748) justification -1: -372 441
[attach-meaning] #366 arith (- 1)
[mk-app] #2759 * #366 #2243
[mk-app] #2762 + #2242 #2759
[mk-app] #2763 <= #2762 #337
[mk-app] #2764 >= #2762 #337
[attach-enode] #2759 0
[attach-enode] #2762 0
[assign] #2763 justification -1: 390
[assign] #2764 justification -1: 390
[mk-app] #2772 = #2222 #2243
[attach-meaning] #366 arith (- 1)
[mk-app] #2773 + #2222 #2759
[mk-app] #2774 <= #2773 #337
[mk-app] #2775 >= #2773 #337
[attach-enode] #2772 0
[attach-enode] #2773 0
[new-match] 0x56096217dc80 #1191 #1190 #1187 #2230 ; #2693
[new-match] 0x56096217dcb8 #1191 #1190 #1187 #2228 ; #2745
[new-match] 0x56096217dcf0 #1191 #1190 #1213 #2411 ; #2515
[new-match] 0x56096217dd28 #1209 #1205 #1212 #2411 ; #2515 (#1213 #1213)
[new-match] 0x56096217dd60 #1191 #1190 #1213 #2239 ; #2527
[new-match] 0x56096217dd98 #1209 #1205 #1212 #2239 ; #2527 (#1213 #1213)
[mk-app] #2771 or #2642 #2674
[instance] 0x56096217dcf0 ; 3
[attach-enode] #2673 3
[attach-enode] #2674 3
[assign] #2674 justification -1: 262
[end-of-instance]
[mk-app] #2769 or #2641 #2514 #2683
[instance] 0x56096217dd28 ; 3
[mk-app] #2783 = #2682 #292
[mk-app] #2781 = #2681 #2682
[attach-enode] #2682 3
[attach-enode] #2676 3
[mk-app] #2770 <= #2531 #337
[attach-enode] #2677 3
[attach-enode] #2678 3
[attach-enode] #2679 3
[attach-enode] #2680 3
[attach-enode] #2681 3
[attach-enode] #2783 3
[attach-enode] #2781 3
[attach-enode] #2683 3
[assign] #2683 justification -1: 263 489
[end-of-instance]
[mk-app] #2757 or #2642 #2725
[instance] 0x56096217dd60 ; 2
[attach-enode] #2724 2
[attach-enode] #2725 2
[assign] #2725 justification -1: 262
[end-of-instance]
[mk-app] #2747 or #2641 #2526 #2734
[instance] 0x56096217dd98 ; 2
[mk-app] #2744 = #2733 #292
[mk-app] #2784 = #2732 #2733
[attach-enode] #2733 2
[attach-enode] #2727 2
[mk-app] #2785 <= #2534 #337
[attach-enode] #2728 2
[attach-enode] #2729 2
[attach-enode] #2730 2
[attach-enode] #2731 2
[attach-enode] #2732 2
[attach-enode] #2744 2
[attach-enode] #2784 2
[attach-enode] #2734 2
[assign] #2734 justification -1: 263 493
[end-of-instance]
[assign] #2708 clause 555 553
[assign] (not #2772) justification -1: -398 386 381
[attach-meaning] #366 arith (- 1)
[mk-app] #2786 * #366 #2531
[mk-app] #2787 + #2410 #2786
[mk-app] #2788 <= #2787 #337
[mk-app] #2789 >= #2787 #337
[attach-enode] #2786 0
[attach-enode] #2787 0
[assign] #2788 justification -1: 495
[assign] #2789 justification -1: 495
[attach-meaning] #366 arith (- 1)
[mk-app] #2790 * #366 #2534
[mk-app] #2791 + #2191 #2790
[mk-app] #2792 <= #2791 #337
[mk-app] #2793 >= #2791 #337
[attach-enode] #2790 0
[attach-enode] #2791 0
[assign] #2792 justification -1: 496
[assign] #2793 justification -1: 496
[new-match] 0x56096211eca8 #1191 #1190 #1187 #2411 ; #2673
[new-match] 0x56096211ece0 #1191 #1190 #1187 #2239 ; #2724
[eq-expl] #2749 cg (#2385 #2193) (#292 #292) ; #2204
[eq-expl] #2750 cg (#2749 #2204) ; #2205
[eq-expl] #2751 cg (#2750 #2205) ; #2230
[new-match] 0x56096211ed18 #1191 #1190 #1212 #2751 ; #2752
[eq-expl] #2752 root
[new-match] 0x56096211ed50 #570 #564 #2752 #1196 ; #2753
[new-match] 0x56096211ed88 #1865 #564 #2752 #1196 ; #2753
[mk-app] #2794 or #2642 #2782
[instance] 0x56096211ed18 ; 3
[attach-enode] #2780 3
[attach-enode] #2782 3
[assign] #2782 justification -1: 262
[end-of-instance]
[mk-app] #2795 * #1196 #2752
[inst-discovered] theory-solving 0 arith# ; #2765
[mk-app] #2796 = #2765 #2795
[instance] 0 #2796
[attach-enode] #2796 0
[end-of-instance]
[mk-app] #2796 Int
[attach-meaning] #2796 arith (- 2)
[mk-app] #2797 * #2796 #2752
[mk-app] #2798 * #366 #2795
[inst-discovered] theory-solving 0 arith# ; #2798
[mk-app] #2799 = #2798 #2797
[instance] 0 #2799
[attach-enode] #2799 0
[end-of-instance]
[mk-app] #2795 + #2797 #2753
[mk-app] #2798 + #2753 #2797
[inst-discovered] theory-solving 0 arith# ; #2798
[mk-app] #2799 = #2798 #2795
[instance] 0 #2799
[attach-enode] #2799 0
[end-of-instance]
[mk-app] #2798 * #1196 #2752
[attach-meaning] #366 arith (- 1)
[mk-app] #2799 * #366 #2753
[mk-app] #2800 + #2798 #2799
[mk-app] #2801 = #2800 #337
[mk-app] #2802 = #2795 #337
[inst-discovered] theory-solving 0 arith# ; #2802
[mk-app] #2803 = #2802 #2801
[instance] 0 #2803
[attach-enode] #2803 0
[end-of-instance]
[mk-app] #2796 or #2422 #2801
[instance] 0x56096211ed50 ; 3
[attach-enode] #2798 3
[attach-enode] #2799 3
[attach-enode] #2800 3
[attach-enode] #2801 3
[mk-app] #2797 <= #2800 #337
[mk-app] #2795 >= #2800 #337
[assign] #2801 justification -1: 78
[end-of-instance]
[mk-app] #2802 or #2777 #2778
[mk-app] #2803 or #2 #2777 #2778
[inst-discovered] theory-solving 0 basic# ; #2803
[mk-app] #2804 = #2803 #2802
[instance] 0 #2804
[attach-enode] #2804 0
[end-of-instance]
[mk-app] #2803 or #2436 #2777 #2778
[instance] 0x56096211ed88 ; 3
[end-of-instance]
[assign] #2797 clause 590 -589
[assign] #2795 clause 591 -589
[mk-app] #2802 = #2232 #2753
[attach-meaning] #366 arith (- 1)
[mk-app] #2804 + #2232 #2799
[mk-app] #2805 <= #2804 #337
[mk-app] #2806 >= #2804 #337
[assign] #2802 justification -1: 555 556 517 386
[attach-enode] #2802 0
[attach-enode] #2804 0
[assign] #2805 justification -1: 594
[assign] #2806 justification -1: 594
[mk-app] #2807 = #2231 #2752
[attach-meaning] #366 arith (- 1)
[mk-app] #2808 * #366 #2752
[mk-app] #2809 + #2231 #2808
[mk-app] #2810 <= #2809 #337
[mk-app] #2811 >= #2809 #337
[assign] #2807 justification -1: 492 588 547 441
[attach-enode] #2807 0
[attach-enode] #2808 0
[attach-enode] #2809 0
[assign] #2810 justification -1: 597
[assign] #2811 justification -1: 597
[assign] #2661 clause 573 -497 -584
[assign] #2713 clause 580 -586 -369
[decide-and-or] #2437 #2432
[push] 3
[assign] (not #2431) decision axiom
[assign] (not #2433) clause -452 451 -450
[assign] (not #2602) clause -538 451 -450 -541
[assign] (not #2600) clause -537 451 -535 -450 -541
[decide-and-or] #2512 #2507
[push] 4
[assign] (not #2506) decision axiom
[decide-and-or] #2618 #2509
[push] 5
[assign] (not #2508) decision axiom
[assign] (not #2612) clause -515 487 -514
[assign] (not #2778) clause -593 487 -514 -596
[assign] (not #2776) clause -592 487 -590 -514 -596
[push] 6
[assign] (not #2630) decision axiom
[assign] (not #2605) clause -526 525 -527
[assign] #2608 clause 529 525
[assign] (not #2770) clause -572 526 -461 -468 -473 -476 -500 -505 -435 -532 -430 -584
[eq-expl] #2634 root
[new-match] 0x56096211fdc0 #570 #564 #2634 #1196 ; #2635
[new-match] 0x56096211fdf8 #1865 #564 #2634 #1196 ; #2635
[eq-expl] #2633 root
[new-match] 0x56096211fe30 #1191 #1190 #1212 #2633 ; #2634
[eq-expl] #2632 root
[new-match] 0x56096211fe68 #170 #169 #2632 ; #2633
[eq-expl] #2631 root
[new-match] 0x56096211fe98 #1816 #344 #2631 ; #2632
[new-match] 0x56096211fec8 #563 #555 #292 #2405 ; #2631
[mk-app] #2812 * #2634 #1196
[mk-app] #2813 * #366 #2812
[mk-app] #2814 + #2635 #2813
[mk-app] #2815 = #2814 #337
[mk-app] #2816 * #1196 #2634
[inst-discovered] theory-solving 0 arith# ; #2812
[mk-app] #2817 = #2812 #2816
[instance] 0 #2817
[attach-enode] #2817 0
[end-of-instance]
[mk-app] #2817 Int
[attach-meaning] #2817 arith (- 2)
[mk-app] #2818 * #2817 #2634
[mk-app] #2819 * #366 #2816
[inst-discovered] theory-solving 0 arith# ; #2819
[mk-app] #2820 = #2819 #2818
[instance] 0 #2820
[attach-enode] #2820 0
[end-of-instance]
[mk-app] #2816 + #2818 #2635
[mk-app] #2819 + #2635 #2818
[inst-discovered] theory-solving 0 arith# ; #2819
[mk-app] #2820 = #2819 #2816
[instance] 0 #2820
[attach-enode] #2820 0
[end-of-instance]
[mk-app] #2819 * #1196 #2634
[attach-meaning] #366 arith (- 1)
[mk-app] #2820 * #366 #2635
[mk-app] #2821 + #2819 #2820
[mk-app] #2822 = #2821 #337
[mk-app] #2823 = #2816 #337
[inst-discovered] theory-solving 0 arith# ; #2823
[mk-app] #2824 = #2823 #2822
[instance] 0 #2824
[attach-enode] #2824 0
[end-of-instance]
[mk-app] #2817 or #2422 #2822
[instance] 0x56096211fdc0 ; 3
[attach-enode] #2819 3
[attach-enode] #2820 3
[attach-enode] #2821 3
[attach-enode] #2822 3
[mk-app] #2818 <= #2821 #337
[mk-app] #2816 >= #2821 #337
[assign] #2822 justification -1: 78
[end-of-instance]
[mk-app] #2823 >= #2634 #337
[mk-app] #2824 not #2823
[mk-app] #2825 >= #2635 #337
[mk-app] #2826 or #2430 #2824 #2825
[mk-app] #2827 or #2824 #2825
[mk-app] #2828 or #2 #2824 #2825
[inst-discovered] theory-solving 0 basic# ; #2828
[mk-app] #2829 = #2828 #2827
[instance] 0 #2829
[attach-enode] #2829 0
[end-of-instance]
[mk-app] #2828 or #2436 #2824 #2825
[instance] 0x56096211fdf8 ; 3
[end-of-instance]
[mk-app] #2827 the_q!model.rec%pow2.? #2633 #1187
[mk-app] #2829 = #2634 #2827
[mk-app] #2830 or #2642 #2829
[instance] 0x56096211fe30 ; 3
[attach-enode] #2827 3
[attach-enode] #2829 3
[assign] #2829 justification -1: 262
[end-of-instance]
[mk-app] #2831 %I #2633
[mk-app] #2832 = #2632 #2831
[mk-app] #2833 or #2391 #2832
[instance] 0x56096211fe68 ; 3
[attach-enode] #2831 3
[attach-enode] #2832 3
[assign] #2832 justification -1: 25
[end-of-instance]
[mk-app] #2834 >= #2632 #337
[mk-app] #2835 not #2834
[mk-app] #2836 >= #2631 #337
[mk-app] #2837 not #2836
[mk-app] #2838 = #2631 #2632
[mk-app] #2839 or #2837 #2838
[mk-app] #2840 not #2839
[mk-app] #2841 or #2835 #2840
[mk-app] #2842 not #2841
[mk-app] #2843 or #2355 #2842
[instance] 0x56096211fe98 ; 3
[attach-enode] #2838 3
[attach-meaning] #366 arith (- 1)
[mk-app] #2844 * #366 #2632
[mk-app] #2845 + #2631 #2844
[mk-app] #2846 <= #2845 #337
[mk-app] #2847 >= #2845 #337
[attach-enode] #2844 3
[attach-enode] #2845 3
[assign] (not #2841) justification -1: 55
[end-of-instance]
[mk-app] #2848 + #292 #2594 #2631
[mk-app] #2849 = #2848 #337
[attach-meaning] #366 arith (- 1)
[mk-app] #2850 + #2594 #2631
[attach-meaning] #366 arith (- 1)
[mk-app] #2851 * #366 #2631
[mk-app] #2852 + #2405 #2851
[mk-app] #2850 = #2852 #292
[inst-discovered] theory-solving 0 arith# ; #2849
[mk-app] #2853 = #2849 #2850
[instance] 0 #2853
[attach-enode] #2853 0
[end-of-instance]
[mk-app] #2853 or #2367 #2850
[instance] 0x56096211fec8 ; 3
[attach-enode] #2851 3
[attach-enode] #2852 3
[attach-enode] #2850 3
[mk-app] #2854 <= #2852 #292
[mk-app] #2855 >= #2852 #292
[assign] #2850 justification -1: 77
[end-of-instance]
[assign] (not #2676) clause -571 572
[assign] #2818 clause 601 -600
[assign] #2816 clause 602 -600
[assign] #2834 clause 607 613
[assign] #2839 clause 612 613
[assign] #2854 clause 615 -614
[assign] #2855 clause 616 -614
[assign] #2781 clause 575 571
[resolve-lit] 0 #2261
[resolve-process] (not #2261)
[resolve-lit] 0 (not #2223)
[resolve-lit] 0 (not #2244)
[resolve-lit] 0 (not #2413)
[resolve-lit] 0 (not #2406)
[resolve-lit] 0 (not #2541)
[resolve-lit] 0 (not #2233)
[resolve-lit] 0 (not #2558)
[resolve-lit] 0 (not #2557)
[resolve-lit] 0 (not #2370)
[resolve-lit] 0 (not #2369)
[resolve-lit] 0 (not #2360)
[resolve-lit] 0 (not #2359)
[resolve-lit] 0 (not #2477)
[resolve-lit] 0 (not #2476)
[resolve-lit] 0 (not #2494)
[resolve-lit] 0 (not #2493)
[resolve-lit] 0 (not #2463)
[resolve-lit] 0 (not #2462)
[resolve-lit] 0 (not #2486)
[resolve-lit] 0 (not #2485)
[resolve-lit] 0 (not #2568)
[resolve-lit] 0 (not #2574)
[resolve-process] #2261
[resolve-lit] 0 #2200
[resolve-process] #2200
[resolve-lit] 0 #2277
[resolve-process] (not #2244)
[resolve-process] #2277
[resolve-lit] 0 (not #2273)
[resolve-lit] 0 (not #2288)
[resolve-process] (not #2273)
[resolve-lit] 0 (not #2227)
[resolve-process] (not #2227)
[resolve-lit] 0 (not #2234)
[resolve-process] (not #2233)
[resolve-lit] 0 #2199
[resolve-lit] 1 (not #1221)
[resolve-process] (not #2568)
[resolve-process] (not #2574)
[resolve-process] (not #2288)
[resolve-lit] 0 #2295
[resolve-process] (not #2234)
[resolve-process] #2295
[resolve-lit] 0 (not #2271)
[resolve-lit] 0 (not #2302)
[resolve-process] (not #2271)
[resolve-lit] 0 (not #2213)
[resolve-process] (not #2213)
[resolve-lit] 0 (not #2224)
[resolve-process] (not #2223)
[resolve-lit] 0 #2308
[resolve-process] (not #2477)
[resolve-lit] 0 (not #2468)
[resolve-process] (not #2476)
[resolve-process] (not #2468)
[resolve-lit] 0 (not #2466)
[resolve-lit] 0 (not #2469)
[resolve-process] (not #2541)
[resolve-lit] 0 (not #2539)
[resolve-lit] 0 (not #2542)
[resolve-process] (not #2466)
[resolve-process] (not #2539)
[resolve-lit] 0 (not #2346)
[resolve-process] (not #2463)
[resolve-lit] 0 (not #2454)
[resolve-process] (not #2462)
[resolve-process] (not #2558)
[resolve-lit] 0 (not #2555)
[resolve-process] (not #2557)
[resolve-process] (not #2542)
[resolve-lit] 0 #2544
[resolve-process] (not #2454)
[resolve-lit] 0 (not #2452)
[resolve-lit] 0 (not #2455)
[resolve-process] (not #2413)
[resolve-lit] 0 (not #2408)
[resolve-lit] 0 (not #2414)
[resolve-process] (not #2555)
[resolve-process] #2544
[resolve-process] (not #2452)
[resolve-process] (not #2408)
[resolve-lit] 0 (not #2212)
[resolve-lit] 0 (not #2206)
[resolve-process] (not #2494)
[resolve-lit] 0 (not #2489)
[resolve-process] (not #2493)
[resolve-process] (not #2486)
[resolve-lit] 0 (not #2482)
[resolve-process] (not #2485)
[resolve-process] (not #2469)
[resolve-lit] 0 #2471
[resolve-process] (not #2455)
[resolve-lit] 0 #2457
[resolve-process] (not #2489)
[resolve-process] (not #2482)
[resolve-process] #2471
[resolve-process] #2457
[resolve-process] (not #2414)
[resolve-process] (not #2406)
[resolve-process] (not #2302)
[resolve-lit] 0 #2304
[resolve-process] (not #2224)
[resolve-process] (not #2212)
[resolve-process] #2304
[resolve-lit] 0 (not #2294)
[resolve-lit] 0 (not #2307)
[resolve-process] (not #2294)
[resolve-lit] 0 (not #2293)
[resolve-process] (not #2293)
[resolve-lit] 0 #2393
[resolve-process] #2393
[resolve-process] (not #2360)
[resolve-lit] 0 (not #2350)
[resolve-process] (not #2359)
[resolve-process] (not #2350)
[resolve-lit] 0 (not #2348)
[resolve-lit] 0 (not #2351)
[resolve-process] (not #2348)
[resolve-process] (not #2370)
[resolve-lit] 0 (not #2364)
[resolve-process] (not #2369)
[resolve-process] (not #2351)
[resolve-lit] 0 #2353
[resolve-process] (not #2346)
[resolve-process] (not #2364)
[resolve-process] #2353
[resolve-process] (not #2307)
[resolve-process] (not #2206)
[resolve-process] #2308
[conflict] #2199 (not #1221)
[pop] 5 7
[attach-enode] #2365 0
[attach-enode] #2366 0
[attach-enode] #2357 0
[attach-enode] #2392 0
[attach-enode] #2358 0
[attach-enode] #2478 0
[attach-enode] #2481 0
[attach-enode] #2409 0
[attach-enode] #2551 0
[attach-enode] #2554 0
[attach-enode] #2460 0
[attach-enode] #2461 0
[attach-enode] #2490 0
[attach-enode] #2491 0
[attach-enode] #2435 0
[attach-enode] #2424 0
[attach-enode] #2425 0
[attach-enode] #2426 0
[attach-enode] #2387 0
[attach-enode] #2569 0
[attach-enode] #2564 0
[attach-enode] #2405 0
[attach-enode] #2594 0
[attach-enode] #2585 0
[attach-enode] #2623 0
[attach-enode] #1212 0
[attach-enode] #1213 0
[attach-enode] #2521 0
[attach-enode] #2522 0
[attach-enode] #2576 0
[attach-enode] #2577 0
[attach-enode] #2578 0
[attach-enode] #2579 0
[attach-enode] #2580 0
[attach-enode] #2648 0
[attach-enode] #2653 0
[attach-enode] #2647 0
[attach-enode] #2649 0
[attach-enode] #2593 0
[attach-enode] #2609 0
[attach-enode] #2610 0
[attach-enode] #2410 0
[attach-enode] #2411 0
[attach-enode] #2531 0
[attach-enode] #2786 0
[attach-enode] #2787 0
[attach-enode] #2534 0
[attach-enode] #2790 0
[attach-enode] #2791 0
[attach-enode] #2385 0
[attach-enode] #2749 0
[attach-enode] #2750 0
[attach-enode] #2751 0
[attach-enode] #2752 0
[attach-enode] #2753 0
[attach-enode] #2799 0
[attach-enode] #2804 0
[attach-enode] #2798 0
[attach-enode] #2800 0
[attach-enode] #2474 0
[attach-enode] #2475 0
[attach-enode] #2547 0
[attach-enode] #2548 0
[attach-enode] #2561 0
[attach-enode] #2562 0
[assign] #2562 axiom
[attach-enode] #2615 0
[attach-enode] #2616 0
[assign] #2616 axiom
[attach-enode] #2663 0
[attach-enode] #2664 0
[assign] #2664 axiom
[attach-enode] #2519 0
[assign] #2519 axiom
[attach-enode] #2715 0
[attach-enode] #2716 0
[assign] #2716 axiom
[assign] #2623 axiom
[assign] #2199 clause 372 -265
[assign] #2308 clause 373 -372
[assign] (not #2200) clause -374 -372
[assign] #2259 clause 397 374
[assign] (not #2261) clause -398 374
[eq-expl] #2240 root
[eq-expl] #2229 root
[new-match] 0x5609620f57b0 #570 #564 #2229 #2240 ; #2260
[new-match] 0x5609620f57e8 #1865 #564 #2229 #2240 ; #2260
[new-match] 0x5609620f5820 #1221 #1217 #2216 ; #2217
[new-match] 0x5609620f5850 #1221 #1217 #2228 ; #2229
[new-match] 0x5609620f5880 #1221 #1217 #2239 ; #2240
[eq-expl] #2215 root
[new-match] 0x5609620f58b0 #170 #169 #2215 ; #2216
[eq-expl] #2193 lit #2199 ; #337
[eq-expl] #337 root
[new-match] 0x5609620f58e0 #170 #169 #2193 ; #2228
[eq-expl] #2191 root
[new-match] 0x5609620f5910 #170 #169 #2191 ; #2239
[eq-expl] #2214 root
[new-match] 0x5609620f5940 #1816 #344 #2214 ; #2215
[new-match] 0x5609620f5970 #548 #546 #2193 #2191 ; #2214
[mk-app] #2364 * #2229 #2240
[mk-app] #2370 * #366 #2364
[mk-app] #2382 + #2260 #2370
[mk-app] #2427 = #2382 #337
[mk-app] #2421 not #570
[mk-app] #2476 or #2421 #2427
[instance] 0x5609620f57b0 ; 1
[attach-enode] #2364 1
[attach-enode] #2370 1
[attach-enode] #2382 1
[attach-enode] #2427 1
[mk-app] #2482 <= #2382 #337
[mk-app] #2489 >= #2382 #337
[assign] #2427 justification -1: 78
[end-of-instance]
[mk-app] #2504 >= #2229 #337
[mk-app] #2505 not #2504
[mk-app] #2550 >= #2260 #337
[mk-app] #2555 or #2507 #2505 #2550
[mk-app] #2558 not #1865
[mk-app] #2570 or #2558 #2507 #2505 #2550
[instance] 0x5609620f57e8 ; 1
[end-of-instance]
[mk-app] #2611 not #1221
[mk-app] #2595 or #2611 #2438 #2440
[instance] 0x5609620f5820 ; 1
[attach-enode] #2439 1
[attach-enode] #2440 1
[end-of-instance]
[mk-app] #2639 or #2611 #2619 #2627
[instance] 0x5609620f5850 ; 1
[attach-enode] #2626 1
[attach-enode] #2627 1
[assign] #2627 justification -1: 265 448
[end-of-instance]
[mk-app] #2573 or #2611 #2526 #2528
[instance] 0x5609620f5880 ; 1
[attach-enode] #2525 1
[attach-enode] #2527 1
[attach-enode] #2528 1
[end-of-instance]
[mk-app] #2621 not #170
[mk-app] #2608 or #2621 #2398
[instance] 0x5609620f58b0 ; 1
[attach-enode] #2398 1
[attach-meaning] #366 arith (- 1)
[mk-app] #2650 >= #2564 #337
[assign] #2398 justification -1: 25
[end-of-instance]
[mk-app] #2644 %I #1399
[mk-app] #2651 = #337 #2644
[attach-meaning] #366 arith (- 1)
[mk-app] #2654 * #366 #2644
[mk-app] #2656 = #2644 #337
[inst-discovered] theory-solving 0 arith# ; #2651
[mk-app] #2654 = #2651 #2656
[instance] 0 #2654
[attach-enode] #2654 0
[end-of-instance]
[mk-app] #2654 or #2621 #2656
[instance] 0x5609620f58e0 ; 1
[attach-enode] #1399 1
[attach-enode] #2644 1
[attach-enode] #2656 1
[assign] #2656 justification -1: 25
[end-of-instance]
[mk-app] #2657 or #2621 #2535
[instance] 0x5609620f5910 ; 1
[attach-enode] #2535 1
[attach-meaning] #366 arith (- 1)
[mk-app] #2658 >= #2791 #337
[assign] #2535 justification -1: 25
[end-of-instance]
[mk-app] #2659 not #1816
[mk-app] #2660 or #2659 #2458
[instance] 0x5609620f5940 ; 1
[attach-enode] #2454 1
[attach-meaning] #366 arith (- 1)
[assign] (not #2457) justification -1: 55
[end-of-instance]
[mk-app] #2667 Add #2191 #337
[mk-app] #2672 * #366 #2667
[mk-app] #2687 + #337 #2191 #2672
[mk-app] #2708 = #2687 #337
[mk-app] #2712 + #2191 #2672
[inst-discovered] theory-solving 0 arith# ; #2687
[mk-app] #2722 = #2687 #2712
[instance] 0 #2722
[attach-enode] #2722 0
[end-of-instance]
[mk-app] #2722 = #2712 #337
[mk-app] #2695 not #548
[mk-app] #2692 or #2695 #2722
[instance] 0x5609620f5970 ; 1
[attach-enode] #2667 1
[attach-enode] #2672 1
[attach-enode] #2712 1
[attach-enode] #2722 1
[mk-app] #2685 <= #2712 #337
[mk-app] #2675 >= #2712 #337
[assign] #2722 justification -1: 76
[end-of-instance]
[assign] #2482 clause 481 -480
[assign] #2489 clause 482 -480
[assign] #2565 clause 443 -490
[assign] #2650 clause 491 -490
[assign] #2792 clause 461 -493
[assign] #2658 clause 494 -493
[assign] #2450 clause 495 498
[assign] #2455 clause 497 498
[assign] #2685 clause 500 -499
[assign] #2675 clause 501 -499
[assign] #2713 clause 460 -461 -369
[assign] #2435 justification -1: 475 490
[assign] #2525 justification -1: 479 493
[mk-app] #2705 = #2214 #2667
[attach-meaning] #366 arith (- 1)
[mk-app] #2669 + #2214 #2672
[mk-app] #2759 <= #2669 #337
[mk-app] #2762 >= #2669 #337
[assign] #2705 justification -1: 372
[attach-enode] #2705 0
[attach-enode] #2669 0
[assign] #2759 justification -1: 502
[assign] #2762 justification -1: 502
[eq-expl] #1213 root
[new-match] 0x56096216b008 #1191 #1190 #1213 #2228 ; #2626
[eq-expl] #1212 root
[new-match] 0x56096216b040 #1209 #1205 #1212 #2228 ; #2626 (#1213 #1213)
[eq-expl] #2387 root
[new-match] 0x56096216b078 #170 #169 #2387 ; #2561
[eq-expl] #2534 root
[new-match] 0x56096216b0a8 #170 #169 #2534 ; #2715
[mk-app] #2763 not #1191
[mk-app] #2764 or #2763 #2746
[instance] 0x56096216b008 ; 2
[attach-enode] #1187 2
[attach-enode] #2745 2
[attach-enode] #2746 2
[assign] #2746 justification -1: 262
[end-of-instance]
[mk-app] #2772 not #1209
[mk-app] #2773 or #2772 #2619 #2755
[instance] 0x56096216b040 ; 2
[mk-app] #2774 = #2754 #292
[mk-app] #2775 = #2753 #2754
[attach-enode] #2754 2
[assign] #2748 justification -1: 492 372
[attach-enode] #2748 2
[attach-enode] #2774 2
[attach-enode] #2775 2
[assign] #2774 justification -1: 506
[attach-enode] #2755 2
[assign] #2755 justification -1: 263 448
[end-of-instance]
[assign] #2440 clause 486 -439
[assign] #2528 clause 489 -488
[mk-app] #2783 = #2229 #292
[mk-app] #2781 <= #2229 #292
[mk-app] #2785 >= #2229 #292
[assign] #2783 justification -1: 487 509 507
[attach-enode] #2783 0
[assign] #2781 justification -1: 510
[assign] #2785 justification -1: 510
[eq-expl] #1187 root
[new-match] 0x56096216b910 #1191 #1190 #1187 #2228 ; #2745
[eq-expl] #2215 lit #2398 ; #2387
[eq-expl] #2216 cg (#2215 #2387) ; #2561
[eq-expl] #2561 root
[new-match] 0x56096216b948 #1191 #1190 #1213 #2216 ; #2439
[new-match] 0x56096216b980 #1209 #1205 #1212 #2216 ; #2439 (#1213 #1213)
[eq-expl] #2191 th arith ; #2667
[eq-expl] #2667 cg (#2191 #2191) (#337 #2193) ; #2214
[eq-expl] #2534 lit #2535 ; #2191
[eq-expl] #2239 cg (#2191 #2534) ; #2715
[eq-expl] #2715 root
[new-match] 0x56096216b9b8 #1191 #1190 #1213 #2239 ; #2527
[new-match] 0x56096216b9f0 #1209 #1205 #1212 #2239 ; #2527 (#1213 #1213)
[mk-app] #2744 the_q!model.rec%pow2.? #2561 #1213
[mk-app] #2784 the_q!model.rec%pow2.? #2561 #1187
[mk-app] #2789 = #2744 #2784
[mk-app] #2793 or #2763 #2789
[instance] 0x56096216b948 ; 2
[attach-enode] #2744 2
[attach-enode] #2784 2
[attach-enode] #2789 2
[assign] #2789 justification -1: 262
[end-of-instance]
[mk-app] #2801 not #2562
[mk-app] #2795 %I #2561
[mk-app] #2802 = #2795 #337
[mk-app] #2805 Sub #2795 #292
[mk-app] #2807 nClip #2805
[mk-app] #2808 I #2807
[mk-app] #2809 the_q!model.rec%pow2.? #2808 #1212
[mk-app] #2810 Mul #1196 #2809
[mk-app] #2811 if #2802 #292 #2810
[mk-app] #2819 = #2744 #2811
[mk-app] #2820 or #2801 #2819
[mk-app] #2821 or #2772 #2801 #2819
[instance] 0x56096216b980 ; 2
[mk-app] #2822 = #2811 #292
[mk-app] #2818 = #2810 #2811
[attach-enode] #2811 2
[attach-enode] #2795 2
[attach-enode] #2802 2
[attach-enode] #2805 2
[attach-enode] #2807 2
[attach-enode] #2808 2
[attach-enode] #2809 2
[attach-enode] #2810 2
[attach-enode] #2822 2
[attach-enode] #2818 2
[attach-enode] #2819 2
[assign] #2819 justification -1: 263 475
[end-of-instance]
[mk-app] #2816 the_q!model.rec%pow2.? #2715 #1213
[mk-app] #2844 the_q!model.rec%pow2.? #2715 #1187
[mk-app] #2845 = #2816 #2844
[mk-app] #2846 or #2763 #2845
[instance] 0x56096216b9b8 ; 2
[attach-enode] #2816 2
[attach-enode] #2844 2
[attach-enode] #2845 2
[assign] #2845 justification -1: 262
[end-of-instance]
[mk-app] #2847 not #2716
[mk-app] #2851 %I #2715
[mk-app] #2852 = #2851 #337
[mk-app] #2850 Sub #2851 #292
[mk-app] #2854 nClip #2850
[mk-app] #2855 I #2854
[mk-app] #2367 the_q!model.rec%pow2.? #2855 #1212
[mk-app] #2853 Mul #1196 #2367
[mk-app] #2355 if #2852 #292 #2853
[mk-app] #2843 = #2816 #2355
[mk-app] #2391 or #2847 #2843
[mk-app] #2833 or #2772 #2847 #2843
[instance] 0x56096216b9f0 ; 2
[mk-app] #2642 = #2355 #292
[mk-app] #2830 = #2355 #2853
[attach-enode] #2355 2
[attach-enode] #2851 2
[attach-enode] #2852 2
[attach-enode] #2850 2
[attach-enode] #2854 2
[attach-enode] #2855 2
[attach-enode] #2367 2
[attach-enode] #2853 2
[attach-enode] #2642 2
[attach-enode] #2830 2
[attach-enode] #2843 2
[assign] #2843 justification -1: 263 479
[end-of-instance]
[assign] #2504 clause 484 -512
[new-match] 0x5609621769e0 #1191 #1190 #1187 #2561 ; #2784
[new-match] 0x560962176a18 #1191 #1190 #1187 #2715 ; #2844
[decide-and-or] #2570 #2507
[push] 2
[assign] (not #2506) decision axiom
[attach-meaning] #366 arith (- 1)
[mk-app] #2436 * #366 #2240
[mk-app] #2828 + #2364 #2436
[attach-enode] #2436 0
[attach-enode] #2828 0
[assign] (not #2550) clause -485 483 -481 -511 -512
[push] 3
[assign] (not #2454) decision axiom
[assign] (not #2452) clause -431 496 -497
[assign] (not #2485) clause -432 431 -370 -369
[assign] #2486 clause 469 432
[resolve-process] true
[resolve-lit] 0 #2452
[resolve-lit] 2 (not #2762)
[resolve-lit] 2 (not #2685)
[conflict] #2452 (not #2762)
[pop] 2 4
[assign] #2452 clause 431 -504
[assign] #2454 clause 496 -431 -497
[assign] #2462 clause 436 -496
[assign] #2463 clause 467 -496
[mk-app] #2436 = #2240 #2260
[attach-meaning] #366 arith (- 1)
[mk-app] #2828 * #366 #2260
[mk-app] #2422 + #2240 #2828
[mk-app] #2817 <= #2422 #337
[mk-app] #2803 >= #2422 #337
[attach-enode] #2436 0
[attach-enode] #2828 0
[attach-enode] #2422 0
[attach-meaning] #366 arith (- 1)
[mk-app] #2796 * #366 #2240
[mk-app] #2794 + #2364 #2796
[attach-enode] #2796 0
[attach-enode] #2794 0
[assign] (not #2436) justification -1: -398 493 490 496 493 372 490 501 500
[resolve-lit] 0 #2261
[resolve-process] (not #2261)
[resolve-lit] 0 (not #2535)
[resolve-lit] 0 (not #2398)
[resolve-lit] 0 (not #2454)
[resolve-lit] 0 (not #2199)
[resolve-lit] 0 (not #2489)
[resolve-lit] 0 (not #2482)
[resolve-lit] 0 (not #2785)
[resolve-lit] 0 (not #2781)
[resolve-lit] 0 (not #2675)
[resolve-lit] 0 (not #2685)
[resolve-process] (not #2454)
[resolve-lit] 0 (not #2452)
[resolve-lit] 0 (not #2455)
[resolve-process] (not #2452)
[resolve-lit] 0 (not #2762)
[resolve-process] (not #2785)
[resolve-lit] 0 (not #2783)
[resolve-process] (not #2781)
[resolve-process] (not #2783)
[resolve-lit] 0 (not #2627)
[resolve-lit] 0 (not #2755)
[resolve-lit] 0 (not #2774)
[resolve-process] (not #2755)
[resolve-lit] 0 (not #2623)
[resolve-process] (not #2774)
[resolve-lit] 0 (not #2748)
[resolve-process] (not #2748)
[resolve-lit] 0 (not #2656)
[resolve-process] (not #2762)
[resolve-lit] 0 (not #2705)
[resolve-process] (not #2705)
[resolve-process] (not #2675)
[resolve-lit] 0 (not #2722)
[resolve-process] (not #2685)
[resolve-process] (not #2455)
[resolve-lit] 0 #2457
[resolve-process] (not #2489)
[resolve-lit] 0 (not #2427)
[resolve-process] (not #2482)
[resolve-process] (not #2722)
[resolve-process] #2457
[resolve-process] (not #2535)
[resolve-process] (not #2656)
[resolve-process] (not #2398)
[resolve-process] (not #2627)
[resolve-lit] 0 (not #1221)
[resolve-process] (not #2427)
[resolve-process] #2261
[resolve-lit] 0 #2200
[resolve-process] #2200
[resolve-process] (not #2199)
[resolve-process] (not #2623)
[conflict] (not #1221)
[pop] 1 2
[attach-enode] #2365 0
[attach-enode] #2366 0
[attach-enode] #2357 0
[attach-enode] #2392 0
[attach-enode] #2358 0
[attach-enode] #2478 0
[attach-enode] #2481 0
[attach-enode] #2409 0
[attach-enode] #2551 0
[attach-enode] #2554 0
[attach-enode] #2460 0
[attach-enode] #2461 0
[attach-enode] #2490 0
[attach-enode] #2491 0
[attach-enode] #2435 0
[attach-enode] #2424 0
[attach-enode] #2425 0
[attach-enode] #2426 0
[attach-enode] #2387 0
[attach-enode] #2569 0
[attach-enode] #2564 0
[attach-enode] #2405 0
[attach-enode] #2594 0
[attach-enode] #2585 0
[attach-enode] #2623 0
[attach-enode] #1212 0
[attach-enode] #1213 0
[attach-enode] #2521 0
[attach-enode] #2522 0
[attach-enode] #2576 0
[attach-enode] #2577 0
[attach-enode] #2578 0
[attach-enode] #2579 0
[attach-enode] #2580 0
[attach-enode] #2648 0
[attach-enode] #2653 0
[attach-enode] #2647 0
[attach-enode] #2649 0
[attach-enode] #2593 0
[attach-enode] #2609 0
[attach-enode] #2610 0
[attach-enode] #2410 0
[attach-enode] #2411 0
[attach-enode] #2531 0
[attach-enode] #2786 0
[attach-enode] #2787 0
[attach-enode] #2534 0
[attach-enode] #2790 0
[attach-enode] #2791 0
[attach-enode] #2385 0
[attach-enode] #2749 0
[attach-enode] #2750 0
[attach-enode] #2751 0
[attach-enode] #2752 0
[attach-enode] #2753 0
[attach-enode] #2799 0
[attach-enode] #2804 0
[attach-enode] #2798 0
[attach-enode] #2800 0
[attach-enode] #2474 0
[attach-enode] #2475 0
[attach-enode] #2547 0
[attach-enode] #2548 0
[attach-enode] #2364 0
[attach-enode] #2370 0
[attach-enode] #2382 0
[attach-enode] #2667 0
[attach-enode] #2672 0
[attach-enode] #2669 0
[assign] #2173 axiom
[assign] #2174 axiom
[assign] #2175 axiom
[assign] #2267 axiom
[assign] #2310 axiom
[assign] #2323 axiom
[assign] #2322 axiom
[assign] #2321 axiom
[assign] #2312 axiom
[assign] #2327 axiom
[assign] #2330 axiom
[assign] #2331 axiom
[assign] #2332 axiom
[assign] #2333 axiom
[assign] #2334 axiom
[assign] #2335 axiom
[assign] #2336 axiom
[assign] #2337 axiom
[assign] #2338 axiom
[assign] #2339 axiom
[assign] #2340 axiom
[assign] #2341 axiom
[assign] #2342 axiom
[assign] #2343 axiom
[assign] #2344 axiom
[assign] #2345 axiom
[attach-enode] #2561 0
[attach-enode] #2562 0
[assign] #2562 axiom
[attach-enode] #2615 0
[attach-enode] #2616 0
[assign] #2616 axiom
[attach-enode] #2663 0
[attach-enode] #2664 0
[assign] #2664 axiom
[attach-enode] #2519 0
[assign] #2519 axiom
[attach-enode] #2715 0
[attach-enode] #2716 0
[assign] #2716 axiom
[assign] #2623 axiom
[assign] (not #1221) axiom
[assign] #1123 clause 256 -453
[assign] #1148 clause 258 -454
[assign] #1210 clause 264 -455
[assign] #1225 clause 267 -456
[assign] #1236 clause 270 -457
[assign] #1255 clause 273 -458
[assign] #1287 clause 278 -459
[assign] #1316 clause 283 -460
[assign] #1352 clause 288 -461
[assign] #1379 clause 293 -462
[assign] #1388 clause 297 -463
[assign] #1397 clause 300 -464
[assign] #1419 clause 303 -465
[assign] #1435 clause 306 -466
[assign] #1471 clause 309 -467
[assign] #1480 clause 312 -468
[assign] #1489 clause 315 -469
[assign] #1503 clause 318 -470
[assign] #1518 clause 321 -471
[assign] #1532 clause 324 -472
[assign] #1546 clause 327 -473
[assign] #1561 clause 330 -474
[assign] #1574 clause 333 -475
[assign] #1590 clause 337 -476
[assign] #1615 clause 340 -477
[assign] #1643 clause 343 -478
[pop] 1 1
[eof]
