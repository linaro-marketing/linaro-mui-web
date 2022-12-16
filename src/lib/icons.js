/**
 @module Icons
*/
import {
  MdAdd,
  MdArrowBack,
  MdBrightness4,
  MdBrightness7,
  MdCancel,
  MdCheckCircle,
  MdClose,
  MdDashboard,
  MdDelete,
  MdEdit,
  MdEmail,
  MdExpandLess,
  MdExpandMore,
  MdGroup,
  MdKeyboardArrowLeft,
  MdKeyboardArrowRight,
  MdLanguage,
  MdGroups,
  MdLock,
  MdMenu,
  MdOndemandVideo,
  MdPermMedia,
  MdPersonOutline,
  MdAnalytics,
  MdPublic,
  MdSave,
  MdSearch,
  MdSettings,
  MdOutlineNotificationsActive,
  MdVisibility,
  MdUnpublished,
  MdVisibilityOff,
} from "react-icons/md";
import {
  FaBuilding,
  FaExternalLinkAlt,
  FaEye,
  FaFilePowerpoint,
  FaGithub,
  FaLinkedin,
  FaPencilAlt,
  FaPhotoVideo,
  FaTimes,
  FaTwitter,
  FaUsers,
  FaVideo,
} from "react-icons/fa";
import {
  BsCollectionPlayFill,
  BsFillSkipStartFill,
  BsFillPlayFill,
} from "react-icons/bs";
import {
  AiOutlineTags,
  AiOutlineLineChart,
  AiOutlineBarChart,
} from "react-icons/ai";
import IconButton from "@mui/material/IconButton";
import Icon from "@mui/material/Icon";
import { GrDrag } from "react-icons/gr";
import PropTypes from "prop-types";
export const dashboardLinksIconMapper = {
  add: MdAdd,
  analytics: MdAnalytics,
  back: MdArrowBack,
  brightness4: MdBrightness4,
  brightness7: MdBrightness7,
  cancel: MdCancel,
  checkCircle: MdCheckCircle,
  close: MdClose,
  companies: FaBuilding,
  dashboard: MdDashboard,
  delete: MdDelete,
  edit: MdEdit,
  email: MdEmail,
  expandLess: MdExpandLess,
  expandMore: MdExpandMore,
  externalLinkAlt: FaExternalLinkAlt,
  github: FaGithub,
  keyboardArrowLeft: MdKeyboardArrowLeft,
  keyboardArrowRight: MdKeyboardArrowRight,
  language: MdLanguage,
  linkedin: FaLinkedin,
  menu: MdMenu,
  ondemandVideo: MdOndemandVideo,
  participants: FaUsers,
  notifications: MdOutlineNotificationsActive,
  pencil: FaPencilAlt,
  permissionsAndGroups: MdGroup,
  personOutline: MdPersonOutline,
  photoVideo: FaPhotoVideo,
  powerpoint: FaFilePowerpoint,
  private: MdLock,
  permissions: MdGroups,
  public: MdPublic,
  resources: MdPermMedia,
  save: MdSave,
  search: MdSearch,
  settings: MdSettings,
  themesAndTags: AiOutlineTags,
  times: FaTimes,
  twitter: FaTwitter,
  unpublished: MdUnpublished,
  video: FaVideo,
  view: FaEye,
  visibility: MdVisibility,
  visibilityOff: MdVisibilityOff,
  line: AiOutlineLineChart,
  bar: AiOutlineBarChart,
  playlist: BsCollectionPlayFill,
  drag: GrDrag,
  playFromStart: BsFillSkipStartFill,
  play: BsFillPlayFill,
};
// export const IconWrapper = ({
//   icon,
//   size,
//   color,
//   relative = false,
//   button = false,
//   ...props
// }) => {
//   const CustomIcon = dashboardLinksIconMapper[icon];
//   const iconColor = color || "inherit";
//   return button ? (
//     <IconButton {...props}>
//       <CustomIcon size={size} />
//     </IconButton>
//   ) : (
//     <Icon
//       size={size}
//       sx={[
//         relative && {
//           position: "relative",
//           "& svg": {
//             position: "absolute",
//             top: 0,
//             left: 0,
//             color: "inherit",
//           },
//         },
//       ]}
//       {...props}
//     >
//       <CustomIcon size={size} color={iconColor} />
//     </Icon>
//   );
// };
// IconWrapper.propTypes = {
//   icon: PropTypes.string.isRequired,
//   size: PropTypes.number,
//   color: PropTypes.string,
//   relative: PropTypes.bool,
//   button: PropTypes.bool,
// };
