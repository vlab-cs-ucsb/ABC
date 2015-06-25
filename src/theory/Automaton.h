/*
 * Automaton.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef THEORY_AUTOMATON_H_
#define THEORY_AUTOMATON_H_

#include<iostream>
#include<string>

#include <glog/logging.h>

namespace Vlab {
namespace Theory {

class Automaton {
public:
	enum class Type : int {
		NONE = 0, BOOL, INT, INTBOOl, STRING
	};

	Automaton(Automaton::Type type);
	Automaton(const Automaton&);
	virtual Automaton_ptr clone() const;
	virtual ~Automaton();

	virtual std::string str() const;
	virtual Automaton::Type getType() const;

	class Name {
	public:
		static const std::string NONE;
		static const std::string BOOL;
		static const std::string INT;
		static const std::string INTBOOl;
		static const std::string STRING;
	};
	friend std::ostream& operator<<(std::ostream& os, const Automaton& automaton);

protected:
	const Automaton::Type type;
private:
	static const int VLOG_LEVEL;
};

typedef Automaton* Automaton_ptr;

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_AUTOMATON_H_ */
