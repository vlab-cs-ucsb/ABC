//
// Created by will on 3/5/16.
//

#ifndef SRC_STRINGRELATION_H_
#define SRC_STRINGRELATION_H_

#include <string>
#include <map>
#include <vector>
#include "MultiTrackAutomaton.h"
#include <glog/logging.h>

namespace Vlab {
namespace Theory {

class StringRelation;
typedef StringRelation *StringRelation_ptr;

class StringRelation {
public:
    enum class Type :
            int {
              NONE = 0, EQ, NOTEQ, INTERSECT, VAR, CONSTANT
            };

    struct Subrelation {
        StringRelation::Type type;
        std::vector<std::string> names;
    };

    StringRelation();
    StringRelation(Type t,std::map<std::string, int> *var_map,std::vector<Subrelation> subrels,
                    size_t ntracks, MultiTrackAutomaton_ptr value_auto);
    virtual ~StringRelation();

    StringRelation(const StringRelation&);
    StringRelation_ptr clone() const;

    StringRelation_ptr combine(StringRelation_ptr other_relation);

    StringAutomaton_ptr get_variable_value_auto(std::string name);
    bool set_variable_value_auto(StringAutomaton_ptr value_auto, std::string name);

    void add_subrelation(Subrelation subrel);
    std::vector<Subrelation> get_subrelation_list();

    MultiTrackAutomaton_ptr get_value_auto();
    bool set_value_auto(MultiTrackAutomaton_ptr value_auto);
    bool update_value_auto(MultiTrackAutomaton_ptr value_auto);

    void set_type(Type type);
    StringRelation::Type get_type() const;

    int get_variable_index(std::string name) const;
    void set_num_tracks(size_t ntracks);
    size_t get_num_tracks() const;

    std::map<std::string, int>* get_variable_track_map();
    void set_variable_track_map(std::map<std::string, int>* track_map);

protected:
    Type type;
    std::map<std::string, int> *var_track_map;
    std::vector<Subrelation> subrelations;
    size_t num_tracks;
    MultiTrackAutomaton_ptr value;

private:
  static const int VLOG_LEVEL;
};


} /* namespace Theory */
} /* namespace Vlab */

#endif //SRC_STRINGRELATION_H_
