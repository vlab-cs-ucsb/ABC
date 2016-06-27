//
// Created by will on 3/5/16.
//

#ifndef SRC_STRINGRELATION_H_
#define SRC_STRINGRELATION_H_

#include <string>
#include <map>
#include <vector>
#include <memory>
#include <glog/logging.h>

namespace Vlab {
namespace Theory {

class StringRelation;
using StringRelation_ptr = StringRelation*;

class StringRelation {
 public:
  enum class Type
    :
    int {
      NONE = 0,
    EQ,
    NOTEQ,
    GT,
    GE,
    LT,
    LE,
    INTERSECT,
    UNION,
    INT_VAR,
    INT_CONSTANT,
    STRING_VAR,
    STRING_CONSTANT,
    REGEX,
    EQ_NO_LAMBDA,
    EQ_ONLY_LAMBDA
  };

  StringRelation();
  StringRelation(Type t, StringRelation_ptr left, StringRelation_ptr right,
                  std::string data, std::map<std::string, int>* trackmap);
  virtual ~StringRelation();

  StringRelation(const StringRelation&);
  StringRelation_ptr clone() const;

  std::string str() const;
  void set_type(Type type);
  StringRelation::Type get_type() const;

  void set_left(StringRelation_ptr left);
  StringRelation_ptr get_left();
  void set_right(StringRelation_ptr right);
  StringRelation_ptr get_right();

  void set_data(std::string data);
  std::string get_data();

  int get_variable_index(std::string name);
  std::map<std::string ,int>* get_term_trackmap();

  bool has_same_trackmap(StringRelation_ptr other_relation);

  std::map<std::string, int>* get_variable_trackmap();
  void set_variable_trackmap(std::map<std::string, int>* trackmap);

  int get_num_tracks();

  friend std::ostream& operator<<(std::ostream& os, const StringRelation& relation);
 protected:
  StringRelation::Type type_;
  StringRelation_ptr left_;
  StringRelation_ptr right_;
  std::string data_;
  std::map<std::string, int>* trackmap_handle_;

 private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif //SRC_STRINGRELATION_H_
