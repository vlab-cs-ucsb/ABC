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
    VAR,
    CONSTANT
  };

  struct Subrelation {
    StringRelation::Type type;
    std::vector<std::string> names;
  };

  StringRelation();
  StringRelation(Type t, std::map<std::string, int>* trackmap, std::vector<Subrelation> subrels,
                 size_t ntracks);
  virtual ~StringRelation();

  StringRelation(const StringRelation&);
  StringRelation_ptr clone() const;

  std::string str() const;
  void set_type(Type type);
  StringRelation::Type get_type() const;
  void set_num_tracks(size_t ntracks);
  size_t get_num_tracks() const;
  int get_variable_index(std::string name);
  std::map<std::string ,int>* get_term_trackmap();

  bool has_same_trackmap(StringRelation_ptr other_relation);
  StringRelation_ptr combine(StringRelation_ptr other_relation);

  void add_subrelation(Subrelation subrel);
  std::vector<Subrelation> get_subrelation_list();
  std::map<std::string, int>* get_variable_trackmap();
  void set_variable_trackmap(std::map<std::string, int>* trackmap);

  friend std::ostream& operator<<(std::ostream& os, const StringRelation& relation);
 protected:
  StringRelation::Type type_;
  std::map<std::string, int>* trackmap_handle_;
  std::vector<Subrelation> subrelations_;
  size_t num_tracks_;

 private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif //SRC_STRINGRELATION_H_
