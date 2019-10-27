


inline Bool State::treeCompress(z3::context &ctx, Addr64 Target_Addr, State_Tag Target_Tag, std::vector<State_Tag> &avoid, ChangeView& change_view, std::hash_map<ULong, Vns> &change_map, std::hash_map<UShort, Vns> &regs_change_map) {
	ChangeView _change_view = { this, &change_view };
	if (branch.empty()) {
		if (guest_start == Target_Addr && status == Target_Tag) {
			ChangeView *_cv = &_change_view;
			do {
				auto state = _cv->elders;
				if (state->regs.record) {
					for (auto offset : *state->regs.record) {
						auto _Where = regs_change_map.lower_bound(offset);
						if (_Where == regs_change_map.end()) {
							regs_change_map[offset] = state->regs.Iex_Get(offset, Ity_I64, ctx);
						}
					}
				}
				for (auto mcm : state->mem.mem_change_map) {
					vassert(mcm.second->record != NULL);
					for (auto offset : *(mcm.second->record)) {
						auto _Where = change_map.lower_bound(offset);
						if (_Where == change_map.end()) {
							auto Address = mcm.first + offset;
							auto p = state->mem.getMemPage(Address);
							vassert(p->user == state->mem.user);
							change_map[Address] = p->unit->Iex_Get(offset, Ity_I64, ctx);
						}
					}
				}
				_cv = _cv->front;
			} while (_cv->front->elders);
			return False;
		}
		for (auto av : avoid) {
			if (av == status) {
				return 2; 
			}
		}
		return True;
	}
	Bool has_branch = False;
	std::vector<State*> ::iterator it = branch.begin();
	while (it != branch.end()) {
		std::hash_map<ULong, Vns> _change_map;
		_change_map.reserve(20);
		std::hash_map<UShort, Vns> _regs_change_map;
		_change_map.reserve(20);
		Bool _has_branch = (*it)->treeCompress(ctx, Target_Addr, Target_Tag, avoid, _change_view, _change_map, _regs_change_map);
		if (!has_branch) {
			has_branch = _has_branch;
		}
		for (auto map_it : _change_map) {
			auto _Where = change_map.lower_bound(map_it.first);
			if (_Where == change_map.end()) {
				change_map[map_it.first] = map_it.second;
			}
			else {
				if (map_it.second.real() && (_Where->second.real()) && ((ULong)(map_it.second) == (ULong)(_Where->second))) {

				}
				else {
					_Where->second = Vns(ctx, Z3_mk_ite(ctx, (*it)->getassert(ctx), map_it.second, _Where->second), 64);
				}
			}
		}
		for (auto map_it : _regs_change_map) {
			auto _Where = regs_change_map.lower_bound(map_it.first);
			if (_Where == regs_change_map.end()) {
				regs_change_map[map_it.first] = map_it.second;
			}
			else {
				if (((map_it.second.real()) && (_Where->second.real())) && ((ULong)(map_it.second) == (ULong)(_Where->second))) {

				}
				else {
					_Where->second = Vns(ctx, Z3_mk_ite(ctx, (*it)->getassert(ctx), map_it.second, _Where->second), 64);
				}
			}
		}
		if (_has_branch == False) {
			delete *it;
			it = branch.erase(it);
			continue;
		}
		else if (_has_branch == 2) {
			delete *it;
			it = branch.erase(it);
			continue;
		}
		it ++;
	}
	if (branch.empty() && status == Fork) {
		return 2;
	}
	else {
		return has_branch;
	}
}



 void State::compress(Addr64 Target_Addr, State_Tag Target_Tag, std::vector<State_Tag> &avoid)
{
	ChangeView change_view= { NULL, NULL };
	std::hash_map<ULong, Vns> change_map;
	change_map.reserve(20);
	std::hash_map<UShort, Vns> regs_change_map;
	regs_change_map.reserve(30);
	auto flag = treeCompress(m_ctx, Target_Addr, Target_Tag, avoid, change_view, change_map, regs_change_map);
	if (flag != True) {
		for (auto map_it : change_map) {
#ifndef  _DEBUG
			std::cout << std::hex << map_it.first << map_it.second << std::endl;
#endif //  _DEBUG
			mem.Ist_Store(map_it.first, map_it.second);
		};
		for (auto map_it : regs_change_map) {
#ifndef  _DEBUG
			std::cout << std::hex << map_it.first << map_it.second << std::endl;
#endif //  _DEBUG
			regs.Ist_Put(map_it.first, map_it.second);
		};
		guest_start = Target_Addr;
		status = NewState;
	}
	else if (flag == True) {
		State *one_state = new State(this, Target_Addr);
		for (auto map_it : change_map) {
#ifndef  _DEBUG
			std::cout << std::hex << map_it.first << map_it.second << std::endl;
#endif //  _DEBUG
			one_state->mem.Ist_Store(map_it.first, map_it.second.translate(*one_state));
		};

		for (auto map_it : regs_change_map) {
#ifndef  _DEBUG
			std::cout << std::hex << map_it.first << map_it.second << std::endl;
#endif //  _DEBUG
			one_state->regs.Ist_Put(map_it.first,  map_it.second.translate(*one_state));
		};
		branch.emplace_back(one_state);
	}
	

	
}