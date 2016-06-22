//
// Created by will on 3/6/16.
//

#include "StringRelation.h"

namespace Vlab {
namespace Theory {

const int StringRelation::VLOG_LEVEL = 25;

StringRelation::StringRelation()
    : type_(Type::NONE),
      var_track_map_(nullptr) {
  num_tracks_ = 0;
}

StringRelation::StringRelation(Type t, std::shared_ptr<std::map<std::string, int>> var_map,
                               std::vector<Subrelation> subrels, size_t ntracks)
    : type_(t),
      var_track_map_(var_map),
      subrelations_(subrels),
      num_tracks_(ntracks) {
}

StringRelation::~StringRelation() {
}

StringRelation::StringRelation(const StringRelation &other)
    : type_(other.type_),
      var_track_map_(other.var_track_map_),
      subrelations_(other.subrelations_),
      num_tracks_(other.num_tracks_) {
}

StringRelation_ptr StringRelation::clone() const {
  return new StringRelation(*this);
}

std::string StringRelation::str() const {
  std::stringstream ss;

  ss << "string relation: ";
  switch (type_) {
    case Type::EQ:
      ss << "=";
      break;
    case Type::NOTEQ:
      ss << "!=";
      break;
    case Type::GT:
      ss << ">";
      break;
    case Type::GE:
      ss << ">=";
      break;
    case Type::LT:
      ss << "<";
      break;
    case Type::LE:
      ss << "<=";
      break;
    case Type::INTERSECT:
      ss << "&";
      break;
    case Type::UNION:
      ss << "|";
      break;
    case Type::VAR:
      ss << "<var>";
      break;
    case Type::CONSTANT:
      ss << "<constant>";
      break;
    default:
      ss << "none";
      break;
  }

  return ss.str();
}

void StringRelation::set_type(Type type) {
  this->type_ = type;
}

StringRelation::Type StringRelation::get_type() const {
  return this->type_;
}

void StringRelation::set_num_tracks(size_t ntracks) {
  this->num_tracks_ = ntracks;
}

size_t StringRelation::get_num_tracks() const {
  return this->var_track_map_->size();
}

int StringRelation::get_variable_index(std::string name) const {
  auto iter = var_track_map_->find(name);
  if (iter == var_track_map_->end()) {
    return -1;
  }
  return iter->second;
}

std::map<std::string ,int>& StringRelation::get_term_track_map() {
  return term_track_map_;
}

bool StringRelation::IsTrackOrderingSame(StringRelation_ptr other_relation) {
  if (term_track_map_.size() not_eq other_relation->term_track_map_.size()) {
    return false;
  }

  for (auto& pair : term_track_map_) {
    auto other_pair = other_relation->term_track_map_.find(pair.first);
    if (other_pair == other_relation->term_track_map_.end()) {
      return false;
    } else if (pair.second not_eq other_pair->second) {
      return false;
    }
  }

  return true;
}

//TODO: Check if the relations are equal...
StringRelation_ptr StringRelation::Combine(StringRelation_ptr other_relation) {
  StringRelation_ptr result_relation = nullptr;
  //if (var_track_map != other_relation->get_variable_track_map()) {
  //  LOG(ERROR)<< "error in stringrelation combine: track maps are not identical";
  //  return nullptr;
  //}
  // combine their relations
  std::vector<Subrelation> subrels(this->subrelations_);
  subrels.insert(subrels.end(), other_relation->subrelations_.begin(), other_relation->subrelations_.end());
  result_relation = new StringRelation(StringRelation::Type::INTERSECT, this->var_track_map_, subrels,
                                       this->var_track_map_->size());
  return result_relation;
}

void StringRelation::add_subrelation(StringRelation::Subrelation subrel) {
  this->subrelations_.push_back(subrel);
}

std::vector<StringRelation::Subrelation> StringRelation::get_subrelation_list() {
  return subrelations_;
}

std::shared_ptr<std::map<std::string, int>> StringRelation::get_variable_track_map() {
  return this->var_track_map_;
}

void StringRelation::set_variable_track_map(std::shared_ptr<std::map<std::string, int>> track_map) {
  this->var_track_map_ = track_map;
}

std::ostream& operator<<(std::ostream& os, const StringRelation& relation) {
  return os << relation.str();
}

} /* namespace Theory */
} /* namespace Vlab */
