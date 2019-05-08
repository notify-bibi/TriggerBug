#pragma once
#ifndef REGISTER_HL
#define REGISTER_HL
#define REGISTER_LEN 1000
//Symbolic
	template<int maxlength>
	inline Symbolic<maxlength>::Symbolic(Z3_context ctx) : m_ctx(ctx) {
		memset(m_fastindex, 0, sizeof(m_fastindex));
	}
    template<int maxlength>
	inline Symbolic<maxlength>::Symbolic(Z3_context ctx, Symbolic<maxlength> *father) : m_ctx(ctx) {
		memcpy(m_fastindex, father->m_fastindex, maxlength);
		m_fastindex[maxlength] = 0;
		int _pcur = maxlength-1;
		DWORD N;
		for (; _pcur > 0; ) {
			if (_BitScanReverse64(&N, ((DWORD64*)(m_fastindex))[_pcur >> 3] & fastMaskBI1[_pcur % 8])) {
				_pcur = ALIGN(_pcur, 8) + (N >> 3);
				_pcur = _pcur - m_fastindex[_pcur] + 1;
				m_ast[_pcur] = Z3_translate(father->m_ctx, father->m_ast[_pcur], m_ctx);
				vassert(m_ast[_pcur] != NULL);
				Z3_inc_ref(m_ctx, m_ast[_pcur]);
				_pcur--;
			}
			else {
				_pcur = ALIGN(_pcur - 8, 8) + 7;
			}
		};
		
	}
	template<int maxlength>
	inline Symbolic<maxlength>::~Symbolic<maxlength>() {
		int _pcur = maxlength - 1;
		DWORD N;
		for (; _pcur > 0; ) {
			if (_BitScanReverse64(&N, ((DWORD64*)(m_fastindex))[_pcur >> 3] & fastMaskBI1[_pcur % 8])) {
				_pcur = ALIGN(_pcur, 8) + (N >> 3);
				_pcur = _pcur - m_fastindex[_pcur] + 1;
				Z3_dec_ref(m_ctx, m_ast[_pcur]);
				_pcur--;
			}
			else {
				_pcur = ALIGN(_pcur - 8, 8) + 7;
			}
		};
	}




//Record
	template<int maxlength>
	Record<maxlength>::Record() { memset(m_flag, 0, sizeof(m_flag)); m_flag[maxlength >> 6] = 0x1; };
	
	template<int maxlength>
	template<int length>
	inline void Record<maxlength>::write(int offset) {
		*(UShort*)(m_flag + (offset >> 6)) |=
			(UShort)
			(
			(offset + length) < ALIGN(offset, 8) + 8
				?
				(maxlength <= 8) ? 0x01ull :
				(maxlength == 16) ? 0b11ull :
				0b1111ull
				:
				(maxlength <= 8) ? 0x11ull :
				(maxlength == 16) ? 0b111ull :
				0b11111ull
			) << ((offset >> 3) % 8);
	}

	template<>
	template<>
	inline void Record<1000>::write<1>(int offset) { m_flag[offset >> 6] |= 1 << ((offset >> 3) % 8); }
	template<>
	template<>
	inline void Record<0x1000>::write<1>(int offset) { m_flag[offset >> 6] |= 1 << ((offset >> 3) % 8); }


	template<int maxlength>
	inline Record<maxlength>::iterator Record<maxlength>::begin() { return iterator(m_flag); }
	template<int maxlength>
	inline Record<maxlength>::iterator Record<maxlength>::end(){ return iterator(m_flag,maxlength); }



//iterator




	template<int maxlength>
	inline Record<maxlength>::iterator::iterator(UChar *flag) :_pcur(0), m_flag((ULong*)flag) {
		DWORD N ;
		for (; ; _pcur += 64) {
			if (_BitScanForward64(&N, m_flag[_pcur >> 6])) {
				_pcur += N;
				return;
			}
		}
	}
	template<int maxlength>
	Record<maxlength>::iterator::iterator(UChar *flag, int length) :_pcur(length >> 3), m_flag((ULong*)flag) {}
	template<int maxlength>
	inline bool  Record<maxlength>::iterator::operator!=(const iterator &src)
	{
		return _pcur < src._pcur;
	}

	template<int maxlength>
	inline void  Record<maxlength>::iterator::operator++()
	{
		unsigned long N ;
		for (;;) {
			if (_BitScanForward64(&N, m_flag[_pcur >> 6] & fastMaskReverse[_pcur % 64])) {
				_pcur = ALIGN(_pcur, 64) + N;
				return;
			}
			else {
				_pcur = ALIGN(_pcur + 64, 64); 
			}
		}
		
	}

	template<int maxlength>
	inline int  Record<maxlength>::iterator::operator*()
	{
		return (_pcur++) << 3;
	}

	template<int maxlength>
	inline const int  Record<maxlength>::iterator::operator*()const
	{
		return (_pcur++) << 3;
	}
	









//Register<maxlength>




    template<int maxlength>
	inline Register<maxlength>::Register(Z3_context ctx, Bool _need_record) :
		m_ctx(ctx),
		record(_need_record?new Record<maxlength>():NULL),
		symbolic(NULL)
	{
	}


    template<int maxlength>
    inline Register<maxlength>::Register(const Register<maxlength> &father_regs) { vassert(0); };
    template<int maxlength>
	inline void Register<maxlength>::operator = (Register<maxlength> &a) { vassert(0); };
    template<int maxlength>
	Register<maxlength>::~Register<maxlength>() { 
		if (symbolic) delete symbolic; 
		if (record) delete record;
	};

    


template<int maxlength>
inline Register<maxlength>::Register<maxlength>(Register<maxlength>& father_regs, Z3_context ctx, Bool _need_record) :
	m_ctx(ctx),
	record(_need_record ? new Record<maxlength>() : NULL),
	symbolic(father_regs.symbolic ? new Symbolic<maxlength>(m_ctx, father_regs.symbolic) : NULL)
{
	memcpy(m_bytes, father_regs.m_bytes, maxlength);
}






inline Z3_ast Reg2Ast(Char nbytes, UChar* m_bytes, UChar *m_fastindex,Z3_ast* m_ast,Z3_context ctx){
	ULong fast_index = GET8(m_fastindex);
	Z3_ast result;
	DWORD index;
	Z3_ast reast;
	auto scan = fast_index&fastMask[nbytes<<3];
	if (_BitScanReverse64(&index, scan)) {
		auto offset = (index >> 3) ;
		auto relen = nbytes - offset - 1;
		auto fast = m_fastindex[offset];
		if (relen) {
			nbytes -= relen;
			auto zsort = Z3_mk_bv_sort(ctx, relen << 3);
			Z3_inc_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
			reast = Z3_mk_unsigned_int64(ctx, GET8(m_bytes + nbytes), zsort);
			Z3_inc_ref(ctx, reast);
			nbytes -= fast;
			result = Z3_mk_concat(ctx, reast, m_ast[nbytes]);
			Z3_dec_ref(ctx, reast);
		}
		else {
			if (nbytes < fast) {
				return Z3_mk_extract(ctx, ((fast) << 3) - 1, (fast - nbytes) << 3, m_ast[nbytes - fast]);
			}
			if (m_fastindex[nbytes] >> 1) {
				result = Z3_mk_extract(ctx, (fast << 3) - 1, 0, m_ast[nbytes - fast]);
				nbytes -= fast;
			}
			else {
				if (nbytes == fast) {
					return m_ast[nbytes - fast];
				}
				else {
					result = m_ast[nbytes - fast];
					nbytes -= fast;
				}
			}
		}
		Z3_inc_ref(ctx, result);
	}
	else {
		auto zsort = Z3_mk_bv_sort(ctx, nbytes<<3);
		Z3_inc_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
		reast = Z3_mk_unsigned_int64(ctx, GET8(m_bytes), zsort);
		Z3_inc_ref(ctx, reast);
		return reast;
	}
	while (nbytes > 0) {
		scan = fast_index & fastMask[nbytes << 3];
		if (_BitScanReverse64(&index, scan)) {
			auto offset = index >> 3;
			auto relen = nbytes - offset - 1;
			auto fast = m_fastindex[offset];
			if (relen) {
				nbytes -= relen;
				auto zsort = Z3_mk_bv_sort(ctx, relen << 3);
				Z3_inc_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
				reast = Z3_mk_unsigned_int64(ctx, GET8(m_bytes + nbytes), zsort);
				Z3_inc_ref(ctx, reast);
				Z3_ast newresult = Z3_mk_concat(ctx, result, reast);
				Z3_inc_ref(ctx, newresult);
				Z3_dec_ref(ctx, result);
				Z3_dec_ref(ctx, reast);
				if (nbytes < fast) {
					Z3_ast ext = Z3_mk_extract(ctx, ((fast) << 3) - 1, (fast - nbytes) << 3, m_ast[nbytes - fast]);
					Z3_inc_ref(ctx, ext);
					Z3_ast result = Z3_mk_concat(ctx, newresult, ext);
					Z3_dec_ref(ctx, newresult);
					Z3_dec_ref(ctx, ext);
					return result;
				}
				else {
					result = Z3_mk_concat(ctx, newresult, m_ast[nbytes - fast]);
					Z3_inc_ref(ctx, result);
					Z3_dec_ref(ctx, newresult);
					nbytes -= fast;
				}
			}
			else {
				if (nbytes < fast) {
					Z3_ast ext = Z3_mk_extract(ctx, ((fast) << 3) - 1, (fast - nbytes) << 3, m_ast[nbytes - fast]);
					Z3_inc_ref(ctx, ext);
					Z3_ast newresult = Z3_mk_concat(ctx, result, ext);
					Z3_dec_ref(ctx, ext);
					Z3_dec_ref(ctx, result);
					return newresult;
				}
				else {
					nbytes -= fast;
					Z3_ast newresult = Z3_mk_concat(ctx, result, m_ast[nbytes]);
					Z3_inc_ref(ctx, newresult);
					Z3_dec_ref(ctx, result);
					result = newresult;
				}
			}
			
		}
		else {
			auto zsort = Z3_mk_bv_sort(ctx, nbytes << 3);
			Z3_inc_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
			reast = Z3_mk_unsigned_int64(ctx, GET8(m_bytes), zsort);
			Z3_inc_ref(ctx, reast);
			Z3_ast newresult = Z3_mk_concat(ctx, result, reast);
			Z3_dec_ref(ctx, reast);
			Z3_dec_ref(ctx, result);
			return newresult;
		}
	}
	return result;

}


//Register<REGISTER_LEN>



inline Register<REGISTER_LEN>::Register(Z3_context ctx, Bool _need_record) :
	m_ctx(ctx),
	record(),
	Need_Record(_need_record)
	{
		memset(m_bytes, 0, sizeof(m_bytes));
		memset(m_fastindex, 0, sizeof(m_fastindex));
		m_fastindex[REGISTER_LEN] = 0;
	}
	inline Register<REGISTER_LEN>::Register(Register<REGISTER_LEN>& father, Z3_context ctx, Bool _need_record) :
		m_ctx(ctx),
		record(),
		Need_Record(_need_record)
	{
		memcpy(m_bytes, father.m_bytes, REGISTER_LEN);
		memcpy(m_fastindex, father.m_fastindex, sizeof(m_fastindex));
		m_fastindex[REGISTER_LEN] = 0;

		int _pcur = REGISTER_LEN - 1;
		DWORD N;
		for (; _pcur > 0; ) {
			if (_BitScanReverse64(&N, ((DWORD64*)(m_fastindex))[_pcur >> 3] & fastMaskBI1[_pcur % 8])) {
				_pcur = ALIGN(_pcur, 8) + (N >> 3);
				_pcur = _pcur - m_fastindex[_pcur] + 1;
				m_ast[_pcur] = Z3_translate(father.m_ctx, father.m_ast[_pcur], m_ctx);
				vassert(m_ast[_pcur] != NULL);
				Z3_inc_ref(m_ctx, m_ast[_pcur]);
				_pcur--;
			}
			else {
				_pcur = ALIGN(_pcur - 8, 8) + 7;
			}
		};
	}
	Register<REGISTER_LEN>::Register(const Register<REGISTER_LEN> &father_regs) { vassert(0); };
   
	inline void Register<REGISTER_LEN>::operator = (Register<REGISTER_LEN> &a) { vassert(0); };
    
	Register<REGISTER_LEN>::~Register() {
		int _pcur = REGISTER_LEN - 1;
		DWORD N;
		for (; _pcur > 0; ) {
			if (_BitScanReverse64(&N, ((DWORD64*)(m_fastindex))[_pcur >> 3] & fastMaskBI1[_pcur % 8])) {
				_pcur = ALIGN(_pcur, 8) + (N >> 3);
				_pcur = _pcur - m_fastindex[_pcur] + 1;
				Z3_dec_ref(m_ctx, m_ast[_pcur]);
				_pcur--;
			}
			else {
				_pcur = ALIGN(_pcur - 8, 8) + 7;
			}
		};
	};

	
    
	inline Variable Register<REGISTER_LEN>::Iex_Get(UInt offset, IRType ty)
	{
#if defined(OPSTR)
		tAMD64REGS(offset, ty2length(ty));
		
#endif // DEBUG

		switch (ty) {
#define lazydef(vectype,nbit,nbytes,compare)								\
	case Ity_##vectype##nbit:														\
		if (compare) {                        		                                \
			return Variable(m_ctx,Reg2Ast(nbytes,m_bytes+offset,m_fastindex+offset,m_ast+offset, m_ctx),nbit);\
		}else{																		\
			return 	Variable(GET##nbytes##(m_bytes + offset), m_ctx);				\
		}			

					  
			lazydef(I,  8, 1, GET1(m_fastindex + offset));
			lazydef(I, 16, 2, GET2(m_fastindex + offset));
		case Ity_F32:		  
			lazydef(I, 32, 4, GET4(m_fastindex + offset));
		case Ity_F64:		  
			lazydef(I, 64, 8, GET8(m_fastindex + offset));
#undef lazydef
		case Ity_I128:
		case Ity_V128: {
			if ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8))) {
				auto ast_vector = Reg2Ast(8, m_bytes + offset, m_fastindex + offset, m_ast + offset, m_ctx);
				Z3_inc_ref(m_ctx, ast_vector);
				
				auto n_ast = Reg2Ast(8, m_bytes + offset + 8, m_fastindex + offset + 8, m_ast + offset + 8, m_ctx);
				Z3_inc_ref(m_ctx, n_ast);
				auto new_vector = Z3_mk_concat(m_ctx, n_ast, ast_vector);
				Z3_inc_ref(m_ctx, new_vector);
				Z3_dec_ref(m_ctx, n_ast);
				Z3_dec_ref(m_ctx, ast_vector);
				return Variable(m_ctx, False, new_vector, 128);
			}
			else {
				return 	Variable(GET16(m_bytes + offset), m_ctx);
			}	
		}
		case Ity_V256: {
			if ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8)) || (GET8(m_fastindex + offset + 16)) || (GET8(m_fastindex + offset + 24))) {
				auto bytes_p = m_bytes + offset;
				auto fast_p = m_fastindex + offset;
				auto ast_p = m_ast + offset;
				auto ast_vector = Reg2Ast(8, bytes_p, fast_p, ast_p, m_ctx);
				Z3_inc_ref(m_ctx, ast_vector);
				for (int count = 8; count <32 ; count +=8) {
					auto n_ast = Reg2Ast(8, bytes_p + count, fast_p + count, ast_p + count, m_ctx);
					Z3_inc_ref(m_ctx, n_ast);
					auto new_vector = Z3_mk_concat(m_ctx, n_ast, ast_vector);
					Z3_inc_ref(m_ctx, new_vector);
					Z3_dec_ref(m_ctx, ast_vector);
					Z3_dec_ref(m_ctx, n_ast);
					ast_vector = new_vector;
				}
				return Variable(m_ctx, False, ast_vector, 256);
			}
			else {
				return 	Variable(GET32(m_bytes + offset), m_ctx);
			}
		}
			
			
			

		default: vex_printf("ty = 0x%x\n", (UInt)ty); vpanic("tIRType");
		}
	}

    
	inline Variable Register<REGISTER_LEN>::Iex_Get_Translate(UInt offset, IRType ty, Z3_context toctx)
	{

#if defined(OPSTR)
		tAMD64REGS(offset, ty2length(ty));
		
#endif // DEBUG
	
		switch (ty) {
#define lazydef(vectype,nbit,nbytes,compare)										\
	case Ity_##vectype##nbit:														\
		if (compare) {                        		                                \
			Z3_ast re = Reg2Ast(nbytes,m_bytes+offset,m_fastindex+offset, m_ast+offset, m_ctx);\
			Z3_inc_ref(m_ctx,re);\
			return Variable(toctx,Z3_translate(m_ctx,re,toctx),m_ctx,re,nbit);			    \
		}else{																		\
			return 	Variable(GET##nbytes##(m_bytes + offset),toctx);				\
		}																			

			lazydef(I,  8, 1, GET1(m_fastindex + offset));
			lazydef(I, 16, 2, GET2(m_fastindex + offset));
		case Ity_F32:
			lazydef(I, 32, 4, GET4(m_fastindex + offset));
		case Ity_F64:
			lazydef(I, 64, 8, GET8(m_fastindex + offset));
#undef lazydef
		case Ity_I128:
		case Ity_V128: {
			if ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8))) {
				auto ast_vector = Reg2Ast(8, m_bytes + offset, m_fastindex + offset, m_ast + offset, m_ctx);
				Z3_inc_ref(m_ctx, ast_vector);

				auto n_ast = Reg2Ast(8, m_bytes + offset + 8, m_fastindex + offset + 8, m_ast + offset + 8, m_ctx);
				Z3_inc_ref(m_ctx, n_ast);
				auto new_vector = Z3_mk_concat(m_ctx, n_ast, ast_vector);
				Z3_inc_ref(m_ctx, new_vector);
				Z3_dec_ref(m_ctx, n_ast);
				Z3_dec_ref(m_ctx, ast_vector);
				return Variable(m_ctx, Z3_translate(m_ctx, new_vector, toctx), m_ctx, new_vector, 128);
			}
			else {
				return 	Variable(GET16(m_bytes + offset), m_ctx);
			}
		}
		case Ity_V256: {
			if ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8)) || (GET8(m_fastindex + offset + 16)) || (GET8(m_fastindex + offset + 24))) {
				auto bytes_p = m_bytes + offset;
				auto fast_p = m_fastindex + offset;
				auto ast_p = m_ast + offset;
				auto ast_vector = Reg2Ast(8, bytes_p, fast_p, ast_p, m_ctx);
				Z3_inc_ref(m_ctx, ast_vector);
				for (int count = 8; count < 32; count += 8) {
					auto n_ast = Reg2Ast(8, bytes_p + count, fast_p + count, ast_p + count, m_ctx);
					Z3_inc_ref(m_ctx, n_ast);
					auto new_vector = Z3_mk_concat(m_ctx, n_ast, ast_vector);
					Z3_inc_ref(m_ctx, new_vector);
					Z3_dec_ref(m_ctx, ast_vector);
					Z3_dec_ref(m_ctx, n_ast);
					ast_vector = new_vector;
				}
				return Variable(m_ctx, Z3_translate(m_ctx, ast_vector, toctx), m_ctx, ast_vector, 256);
			}
			else {
				return 	Variable(GET32(m_bytes + offset), m_ctx);
			}
		}
		default: vex_printf("ty = 0x%x\n", (UInt)ty); vpanic("tIRType");
		}
	}
	
	inline void Register<REGISTER_LEN>::Ist_Put(UInt offset, Variable &ir)
	{
#if defined(OPSTR)
		tAMD64REGS(offset, ir.bitn >> 3);
		
#endif // DEBUG



		switch (ir.bitn) {
#define lazydef(nbit,nbytes,fastindex_method) 					\
	case nbit:													\
		if (GET##nbytes(m_fastindex + offset))					\
		{														\
			clear(offset, nbytes);								\
			if (ir.symbolic()) {						\
				fastindex_method;								\
				m_ast[offset]=ir;								\
				Z3_inc_ref(m_ctx, m_ast[offset]);				\
			}													\
			else {												\
				SET##nbytes(m_fastindex + offset, 0);		    \
				SET##nbytes(m_bytes + offset, ir);				\
			}													\
		}else{												    \
			if (ir.symbolic()) {						\
				fastindex_method;								\
				m_ast[offset]=ir;								\
				Z3_inc_ref(m_ctx, m_ast[offset]);				\
			}													\
			else {												\
				SET##nbytes(m_bytes + offset, ir);				\
			}													\
		}														\
		if (Need_Record)  record.write<nbytes>( offset);		\
		return;

			lazydef( 8, 1, SET1(m_fastindex + offset, 0x01));
			lazydef(16, 2, SET2(m_fastindex + offset, 0x0201));
			lazydef(32, 4, SET4(m_fastindex + offset, 0x04030201));
			lazydef(64, 8, SET8(m_fastindex + offset, 0x0807060504030201));

#undef lazydef
		case 128:
			if ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8))) {
				clear(offset, 8); clear(offset + 8, 8); 
				if (ir.symbolic()) {
					m_ast[offset] = ir;
					Z3_inc_ref(m_ctx, m_ast[offset]);
					SET16(m_fastindex + offset, _mm_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09));
				}
				else {
					SET16(m_fastindex + offset, _mm_set1_epi64x(0));
					SET16(m_bytes + offset, ir);
				}
			}
			else {
				if (ir.symbolic()) {
					m_ast[offset] = ir;
					Z3_inc_ref(m_ctx, m_ast[offset]);
					SET16(m_fastindex + offset, _mm_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09));
				}
				else {
					SET16(m_bytes + offset, ir);
				}
			}
			if (Need_Record)  record.write<16>(offset);
			return;
		case 256:
			if ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8)) || (GET8(m_fastindex + offset + 16)) || (GET8(m_fastindex + offset + 24))) {
				clear(offset, 8); clear(offset + 8, 8); clear(offset + 16, 8); clear(offset + 24, 8);
				if (ir.symbolic()) {
					m_ast[offset] = ir;
					Z3_inc_ref(m_ctx, m_ast[offset]);
					SET32(m_fastindex + offset, _mm256_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09, 0x1817161514131211, 0x201f1e1d1c1b1a19));
				}
				else {
					SET32(m_fastindex + offset, _mm256_set1_epi64x(0));
					SET32(m_bytes + offset, ir);
				}
			}
			else {
				if (ir.symbolic()) {
					m_ast[offset] = ir;
					Z3_inc_ref(m_ctx, m_ast[offset]);
					SET32(m_fastindex + offset, _mm256_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09, 0x1817161514131211, 0x201f1e1d1c1b1a19));
				}
				else {
					SET32(m_bytes + offset, ir);
				}
			}
			if (Need_Record) record.write<32>(offset);
			return;
		default:  vpanic("??wtfk??");
		}
	}
	template<memTAG Tag>
	inline void Register<REGISTER_LEN>::Ist_Put(UInt offset, Variable &ir)
	{
#if defined(OPSTR)
		tAMD64REGS(offset, ir.bitn >> 3);
		
#endif // DEBUG


		switch (ir.bitn) {										
#define lazydef(nbit,nbytes,fastindex_method) 					\
	case nbit:													\
		if (GET##nbytes(m_fastindex + offset))					\
		{														\
			clear(offset, nbytes);								\
			if (Tag == e_symbolic) {							\
				fastindex_method;								\
				m_ast[offset]=ir;								\
				Z3_inc_ref(m_ctx, m_ast[offset]);				\
			}													\
			else {												\
				SET##nbytes(m_fastindex + offset, 0);		    \
				SET##nbytes(m_bytes + offset, ir);				\
			}													\
		}else{												    \
			if (Tag == e_symbolic) {							\
				fastindex_method;								\
				m_ast[offset]=ir;								\
				Z3_inc_ref(m_ctx, m_ast[offset]);				\
			}													\
			else {												\
				SET##nbytes(m_bytes + offset, ir);				\
			}													\
		}														\
		if (Need_Record)  record.write<nbytes>( offset);		\
		return;

			lazydef(8, 1, SET1(m_fastindex + offset, 0x01));
			lazydef(16, 2, SET2(m_fastindex + offset, 0x0201));
			lazydef(32, 4, SET4(m_fastindex + offset, 0x04030201));
			lazydef(64, 8, SET8(m_fastindex + offset, 0x0807060504030201));

#undef lazydef
		case 128:
			if ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8))) { 
				clear(offset, 8); clear(offset + 8, 8);
				if (Tag == e_symbolic) {
					m_ast[offset] = ir;
					Z3_inc_ref(m_ctx, m_ast[offset]);
					SET16(m_fastindex + offset, _mm_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09));
				}
				else {
					SET16(m_fastindex + offset, _mm_set1_epi64x(0));
					SET16(m_bytes + offset, ir);
				}
			}
			else {
				if (Tag == e_symbolic) {
					m_ast[offset] = ir;
					Z3_inc_ref(m_ctx, m_ast[offset]);
					SET16(m_fastindex + offset, _mm_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09));
				}
				else {
					SET16(m_bytes + offset, ir);
				}
			}
			if (Need_Record)  record.write<16>(offset);
			return;
		case 256:
			if ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8)) || (GET8(m_fastindex + offset + 16)) || (GET8(m_fastindex + offset + 24))) {
				clear(offset, 8); clear(offset + 8, 8); clear(offset + 16, 8); clear(offset + 24, 8);
				if (Tag == e_symbolic) {
					m_ast[offset] = ir;
					Z3_inc_ref(m_ctx, m_ast[offset]);
					SET32(m_fastindex + offset, _mm256_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09, 0x1817161514131211, 0x201f1e1d1c1b1a19));
				}
				else {
					SET32(m_fastindex + offset, _mm256_set1_epi64x(0));
					SET32(m_bytes + offset, ir);
				}
			}
			else {
				if (Tag == e_symbolic) {
					m_ast[offset] = ir;
					Z3_inc_ref(m_ctx, m_ast[offset]);
					SET32(m_fastindex + offset, _mm256_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09, 0x1817161514131211, 0x201f1e1d1c1b1a19));
				}
				else {
					SET32(m_bytes + offset, ir);
				}
			}
			if (Need_Record) record.write<32>(offset);
			return;
		default:  vpanic("??wtfk??");
		}
	}
    
	inline void Register<REGISTER_LEN>::clear(UInt org_offset, Char length)//length=nbytes
	{
		auto fastR = m_fastindex[org_offset + length] - 1;
		if (fastR > 0) {
			auto index = org_offset + length - fastR;
			auto sort_size = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast[index]));

			register auto AstR = Z3_mk_extract(m_ctx, sort_size - 1, (fastR << 3), m_ast[index]);
			Z3_inc_ref(m_ctx, AstR);
			m_ast[org_offset + length] = AstR;
			SETFAST(m_fastindex + org_offset + length, (sort_size >> 3) - fastR);
			if (fastR > length) {
				register auto AstL = Z3_mk_extract(m_ctx, ((fastR - length) << 3) - 1, 0, m_ast[index]);
				Z3_inc_ref(m_ctx, AstL);
				Z3_dec_ref(m_ctx, m_ast[index]);
				m_ast[index] = AstL;
				return;
			}
			else if (fastR == length) {
				Z3_dec_ref(m_ctx, m_ast[index]);
				return;
			}
			length -= fastR;
			Z3_dec_ref(m_ctx, m_ast[index]);
		}
		auto fastL = m_fastindex[org_offset] - 1;
		if (fastL > 0) {
			auto index = org_offset - fastL;
			auto sort_size = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast[index])) >> 3;
			register auto newAst = Z3_mk_extract(m_ctx, ((fastL) << 3) - 1, 0, m_ast[index]);
			Z3_inc_ref(m_ctx, newAst);
			Z3_dec_ref(m_ctx, m_ast[index]);
			m_ast[index] = newAst;
			org_offset += (sort_size - fastL);
			length -= (sort_size - fastL);
		}
		DWORD index;
		ULong fast_index = GET8(m_fastindex + org_offset);
		while (length > 0) {
			if (_BitScanReverse64(&index, fast_index & fastMaskB[length])) {
				index >>= 3;
				auto fast = m_fastindex[org_offset + index] - 1;
				length = index - fast;
				Z3_dec_ref(m_ctx, m_ast[org_offset + length]);
			}
			else {
				return;
			}
		}
	}

	inline void Register<REGISTER_LEN>::ShowRegs() {
		printf("\nrax%16llx\n", GET8(m_bytes + 16));
		printf("rbx%16llx\n", GET8(m_bytes + 40));
		printf("rcx%16llx\n", GET8(m_bytes + 24));
		printf("rdx%16llx\n", GET8(m_bytes + 32));

		printf("rsi%16llx\n", GET8(m_bytes + 64));
		printf("rdi%16llx\n", GET8(m_bytes + 72));
		printf("rbp%16llx\n", GET8(m_bytes + 56));
		printf("rsp%16llx\n", GET8(m_bytes + 48));
		printf("rip%16llx\n", GET8(m_bytes + 184));

		printf("r8 %16llx\n", GET8(m_bytes + 80));
		printf("r9 %16llx\n", GET8(m_bytes + 88));
		printf("r10%16llx\n", GET8(m_bytes + 96));
		printf("r11%16llx\n", GET8(m_bytes + 104));
		printf("r12%16llx\n", GET8(m_bytes + 112));
		printf("r13%16llx\n", GET8(m_bytes + 120));
		printf("r14%16llx\n", GET8(m_bytes + 128));
		printf("r15%16llx\n", GET8(m_bytes + 136));
	}







//Register<maxlength>



#define m_fastindex symbolic->m_fastindex
#define m_ast symbolic->m_ast



template<int maxlength>
inline Variable Register<maxlength>::Iex_Get(UInt offset, IRType ty){
//#if defined(_DEBUG)&&defined(OPSTR)
//	tAMD64REGS(offset, ty2length(ty));
//#endif // DEBUG
//
	switch (ty) {
#define lazydef(vectype,nbit,nbytes,compare)								\
	case Ity_##vectype##nbit:														\
		if (symbolic&&compare) {                        		                    \
			return Variable(m_ctx,Reg2Ast(nbytes,m_bytes+offset,m_fastindex+offset, m_ast+offset, m_ctx),nbit);\
		}else{																		\
			return 	Variable(GET##nbytes##(m_bytes + offset), m_ctx);				\
		}																			

		lazydef(I,  8, 1, GET1(m_fastindex + offset));
		lazydef(I, 16, 2, GET2(m_fastindex + offset));
	case Ity_F32:		  
		lazydef(I, 32, 4, GET4(m_fastindex + offset));
	case Ity_F64:		  
		lazydef(I, 64, 8, GET8(m_fastindex + offset));
#undef lazydef
	case Ity_I128:
	case Ity_V128: {
		if (symbolic && ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8)))) {
			auto ast_vector = Reg2Ast(8, m_bytes + offset, m_fastindex + offset, m_ast + offset, m_ctx);
			Z3_inc_ref(m_ctx, ast_vector);

			auto n_ast = Reg2Ast(8, m_bytes + offset + 8, m_fastindex + offset + 8, m_ast + offset + 8, m_ctx);
			Z3_inc_ref(m_ctx, n_ast);
			auto new_vector = Z3_mk_concat(m_ctx, n_ast, ast_vector);
			Z3_inc_ref(m_ctx, new_vector);
			Z3_dec_ref(m_ctx, n_ast);
			Z3_dec_ref(m_ctx, ast_vector);
			return Variable(m_ctx, False, new_vector, 128);
		}
		else {
			return 	Variable(GET16(m_bytes + offset), m_ctx);
		}
	}
	case Ity_V256: {
		if (symbolic && ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8)) || (GET8(m_fastindex + offset + 16)) || (GET8(m_fastindex + offset + 24)))) {
			auto bytes_p = m_bytes + offset;
			auto fast_p = m_fastindex + offset;
			auto ast_p = m_ast + offset;
			auto ast_vector = Reg2Ast(8, bytes_p, fast_p, ast_p, m_ctx);
			Z3_inc_ref(m_ctx, ast_vector);
			for (int count = 8; count < 32; count += 8) {
				auto n_ast = Reg2Ast(8, bytes_p + count, fast_p + count, ast_p + count, m_ctx);
				Z3_inc_ref(m_ctx, n_ast);
				auto new_vector = Z3_mk_concat(m_ctx, n_ast, ast_vector);
				Z3_inc_ref(m_ctx, new_vector);
				Z3_dec_ref(m_ctx, ast_vector);
				Z3_dec_ref(m_ctx, n_ast);
				ast_vector = new_vector;
			}
			return Variable(m_ctx, False, ast_vector, 256);
		}
		else {
			return 	Variable(GET32(m_bytes + offset), m_ctx);
		}
	}
	default: vex_printf("ty = 0x%x\n", (UInt)ty); vpanic("tIRType");
	}
}

template<int maxlength>
inline Variable Register<maxlength>::Iex_Get_Translate(UInt offset, IRType ty, Z3_context toctx) { 
//#if defined(_DEBUG)&&defined(OPSTR)
//	tAMD64REGS(offset, ty2length(ty));
//#endif // DEBUG
	
	switch (ty) {
#define lazydef(vectype,nbit,nbytes,compare)										\
	case Ity_##vectype##nbit:														\
		if (symbolic&&compare) {                        		                    \
			Z3_ast re = Reg2Ast(nbytes,m_bytes+offset,m_fastindex+offset, m_ast+offset, m_ctx);\
			Z3_inc_ref(m_ctx,re);\
			return Variable(toctx,Z3_translate(m_ctx,re,toctx),m_ctx,re,nbit);			    \
		}else{																		\
			return 	Variable(GET##nbytes##(m_bytes + offset),toctx);				\
		}																			

		lazydef(I,  8, 1, GET1(m_fastindex + offset));
		lazydef(I, 16, 2, GET2(m_fastindex + offset));
	case Ity_F32:
		lazydef(I, 32, 4, GET4(m_fastindex + offset));
	case Ity_F64:	
		lazydef(I, 64, 8, GET8(m_fastindex + offset));
#undef lazydef
	case Ity_I128:
	case Ity_V128: {
		if (symbolic && ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8)))) {
			auto ast_vector = Reg2Ast(8, m_bytes + offset, m_fastindex + offset, m_ast + offset, m_ctx);
			Z3_inc_ref(m_ctx, ast_vector);

			auto n_ast = Reg2Ast(8, m_bytes + offset + 8, m_fastindex + offset + 8, m_ast + offset + 8, m_ctx);
			Z3_inc_ref(m_ctx, n_ast);
			auto new_vector = Z3_mk_concat(m_ctx, n_ast, ast_vector);
			Z3_inc_ref(m_ctx, new_vector);
			Z3_dec_ref(m_ctx, n_ast);
			Z3_dec_ref(m_ctx, ast_vector);
			return Variable(m_ctx, Z3_translate(m_ctx, new_vector, toctx), m_ctx, new_vector, 128);
		}
		else {
			return 	Variable(GET16(m_bytes + offset), m_ctx);
		}
	}
	case Ity_V256: {
		if (symbolic && ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8)) || (GET8(m_fastindex + offset + 16)) || (GET8(m_fastindex + offset + 24)))) {
			auto bytes_p = m_bytes + offset;
			auto fast_p = m_fastindex + offset;
			auto ast_p = m_ast + offset;
			auto ast_vector = Reg2Ast(8, bytes_p, fast_p, ast_p, m_ctx);
			Z3_inc_ref(m_ctx, ast_vector);
			for (int count = 8; count < 32; count += 8) {
				auto n_ast = Reg2Ast(8, bytes_p + count, fast_p + count, ast_p + count, m_ctx);
				Z3_inc_ref(m_ctx, n_ast);
				auto new_vector = Z3_mk_concat(m_ctx, n_ast, ast_vector);
				Z3_inc_ref(m_ctx, new_vector);
				Z3_dec_ref(m_ctx, ast_vector);
				Z3_dec_ref(m_ctx, n_ast);
				ast_vector = new_vector;
			}
			return Variable(m_ctx, Z3_translate(m_ctx, ast_vector, toctx), m_ctx, ast_vector, 256);
		}
		else {
			return 	Variable(GET32(m_bytes + offset), m_ctx);
		}
	}
	default: vex_printf("ty = 0x%x\n", (UInt)ty); vpanic("tIRType");
	}

}


template<int maxlength>
template<memTAG Tag>
inline void Register<maxlength>::Ist_Put(UInt offset, Variable &ir) { 
//#if defined(_DEBUG)&&defined(OPSTR)
//	tAMD64REGS(offset, ir.bitn >> 3);
//	ir.tostr();
//#endif // DEBUG
//	
	switch (ir.bitn) {
#define lazydef(nbit,nbytes,fastindex_method) 							\
	case nbit:															\
		if(symbolic){													\
			if (GET##nbytes(m_fastindex + offset))						\
			{															\
				clear(offset, nbytes);									\
				if (Tag == e_symbolic) {								\
					fastindex_method;									\
					m_ast[offset] = ir;									\
					Z3_inc_ref(m_ctx, m_ast[offset]);					\
				}														\
				else {													\
					SET##nbytes(m_fastindex + offset, 0);				\
					SET##nbytes(m_bytes + offset, ir);					\
				}														\
			}															\
			else {														\
				if (Tag == e_symbolic) {								\
					fastindex_method;									\
					m_ast[offset] = ir;									\
					Z3_inc_ref(m_ctx, m_ast[offset]);					\
				}														\
				else {													\
					SET##nbytes(m_bytes + offset, ir);					\
				}														\
			}															\
																		\
		}else{															\
			if (Tag == e_symbolic) {									\
				symbolic = new Symbolic<maxlength>(m_ctx);				\
				fastindex_method;										\
				m_ast[offset] = ir;										\
				Z3_inc_ref(m_ctx, m_ast[offset]);						\
			}															\
			else {														\
				SET##nbytes(m_bytes + offset, ir);						\
			}															\
		}																\
		if (record)  record->write<nbytes>( offset);					\
		return;														
		

		lazydef( 8, 1, SET1(m_fastindex + offset, 0x01));
		lazydef(16, 2, SET2(m_fastindex + offset, 0x0201));
		lazydef(32, 4, SET4(m_fastindex + offset, 0x04030201));
		lazydef(64, 8, SET8(m_fastindex + offset, 0x0807060504030201));

#undef lazydef
	case 128:
		if (symbolic) {
			if ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8))) {
				clear(offset, 8); clear(offset + 8, 8);
				if (Tag == e_symbolic) {
					m_ast[offset] = ir;
					Z3_inc_ref(m_ctx, m_ast[offset]);
					SET16(m_fastindex + offset, _mm_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09));
				}
				else {
					SET16(m_fastindex + offset, _mm_set1_epi64x(0));
					SET16(m_bytes + offset, ir);
				}
			}
			else {
				if (Tag == e_symbolic) {
					m_ast[offset] = ir;
					Z3_inc_ref(m_ctx, m_ast[offset]);
					SET16(m_fastindex + offset, _mm_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09));
				}
				else {
					SET16(m_bytes + offset, ir);
				}
			}
		}
		else {
			if (Tag == e_symbolic) {
				symbolic = new Symbolic<maxlength>(m_ctx);	
				m_ast[offset] = ir;
				Z3_inc_ref(m_ctx, m_ast[offset]);
				SET16(m_fastindex + offset, _mm_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09));
			}
			else {
				SET16(m_bytes + offset, ir);
			}
		}
		if (record)  record->write<16>(offset);				
		return;
	case 256:
		if (symbolic) {
			if ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8)) || (GET8(m_fastindex + offset + 16)) || (GET8(m_fastindex + offset + 24))) {
				clear(offset, 8); clear(offset + 8, 8); clear(offset + 16, 8); clear(offset + 24, 8);
				if (Tag == e_symbolic) {
					m_ast[offset] = ir;
					Z3_inc_ref(m_ctx, m_ast[offset]);
					SET32(m_fastindex + offset, _mm256_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09, 0x1817161514131211, 0x201f1e1d1c1b1a19));
				}
				else {
					SET32(m_fastindex + offset, _mm256_set1_epi64x(0));
					SET32(m_bytes + offset, ir);
				}
			}
			else {
				if (Tag == e_symbolic) {
					m_ast[offset] = ir;
					Z3_inc_ref(m_ctx, m_ast[offset]);
					SET32(m_fastindex + offset, _mm256_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09, 0x1817161514131211, 0x201f1e1d1c1b1a19));
				}
				else {
					SET32(m_bytes + offset, ir);
				}
			}
		}
		else {
			if (Tag == e_symbolic) {
				symbolic = new Symbolic<maxlength>(m_ctx);
				m_ast[offset] = ir;
				Z3_inc_ref(m_ctx, m_ast[offset]);
				SET32(m_fastindex + offset, _mm256_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09, 0x1817161514131211, 0x201f1e1d1c1b1a19));
			}
			else {
				SET32(m_bytes + offset, ir);
			}
		}
		if (record)  record->write<32>(offset);
		return;
	default:  vpanic("??wtfk??");
	}
}

template<int maxlength>
inline void Register<maxlength>::clear(UInt org_offset, Char length) {
	auto fastR = m_fastindex[org_offset + length] - 1;
	if (fastR > 0) {
		auto index = org_offset + length - fastR;
		auto sort_size = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast[index]));

		register auto AstR = Z3_mk_extract(m_ctx, sort_size - 1, (fastR << 3), m_ast[index]);
		Z3_inc_ref(m_ctx, AstR);
		m_ast[org_offset + length] = AstR;
		SETFAST(m_fastindex + org_offset + length, (sort_size >> 3) - fastR);
		if (fastR > length) {
			register auto AstL = Z3_mk_extract(m_ctx, ((fastR - length) << 3) - 1, 0, m_ast[index]);
			Z3_inc_ref(m_ctx, AstL);
			Z3_dec_ref(m_ctx, m_ast[index]);
			m_ast[index] = AstL;
			return;
		}
		else if (fastR == length) {
			Z3_dec_ref(m_ctx, m_ast[index]);
			return;
		}
		length -= fastR;
		Z3_dec_ref(m_ctx, m_ast[index]);
	}
	auto fastL = m_fastindex[org_offset] - 1;
	if (fastL > 0) {
		auto index = org_offset - fastL;
		auto sort_size = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast[index])) >> 3;
		register auto newAst = Z3_mk_extract(m_ctx, ((fastL) << 3) - 1, 0, m_ast[index]);
		Z3_inc_ref(m_ctx, newAst);
		Z3_dec_ref(m_ctx, m_ast[index]);
		m_ast[index] = newAst;
		org_offset += (sort_size - fastL);
		length -= (sort_size - fastL);
	}
	DWORD index;
	ULong fast_index = GET8(m_fastindex + org_offset);
	while (length > 0) {
		if (_BitScanReverse64(&index, fast_index & fastMaskB[length])) {
			index >>= 3;
			auto fast = m_fastindex[org_offset + index] - 1;
			length = index - fast;
			Z3_dec_ref(m_ctx, m_ast[org_offset + length]);
		}
		else {
			return;
		}
	}
}


#undef m_fastindex
#undef m_ast
#undef registercodedef
#undef GETASTSIZE

template<int maxlength>
inline void Register<maxlength>::write_regs(int offset,void* addr,  int length){memcpy(m_bytes + offset, addr, length);}
template<int maxlength>
inline void Register<maxlength>::read_regs(int offset, void* addr, int length){memcpy(addr, m_bytes + offset, length);}







#endif //REGISTER_HL

