//
// Created by will on 3/5/16.
//

#ifndef SRC_StringRelation_H
#define SRC_StringRelation_H

#include <string>
#include <map>
#include <vector>
#include <glog/logging.h>

namespace Vlab {
namespace Theory {

class StringRelation;
typedef StringRelation *StringRelation_ptr;

class StringRelation {
public:
    enum class Type :
            int {
              NONE = 0, EQ, NOTEQ, INTERSECT, VAR
            };

    StringRelation();
    StringRelation(Type t,std::map<std::string, int> var_map,size_t ntracks);

    virtual ~StringRelation();

    StringRelation(const StringRelation&);
    StringRelation_ptr clone() const;

    StringRelation_ptr combine(StringRelation_ptr other_relation);

    void addVariable(std::string name, int track);

    void setType(Type type);
    StringRelation::Type getType() const;

    int getVariableIndex(std::string name) const;
    void setNumTracks(size_t ntracks);
    size_t getNumTracks() const;

    std::map<std::string, int> getVariableTrackMap();
    void setVariableTrackMap(std::map<std::string, int);

protected:
    Type type;
    std::map<std::string, int> var_track_map;
    size_t num_tracks;

private:
  static const int VLOG_LEVEL;
};


} /* namespace Theory */
} /* namespace Vlab */

#endif //SRC_StringRelation_H
