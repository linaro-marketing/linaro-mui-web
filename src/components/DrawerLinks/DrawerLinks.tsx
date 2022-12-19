// Generated with util/create-component.js
import React, { useState } from "react";
import List from "@mui/material/List";
import ListItem from "@mui/material/ListItem";
import ListItemIcon from "@mui/material/ListItemIcon";
import ListItemText from "@mui/material/ListItemText";
import ExpandIcon from "@mui/icons-material/ExpandMore";
import Collapse from "@mui/material/Collapse";
import { useTheme } from "@mui/material/styles";
import Linked from "components/Linked/Linked";
import { DrawerLinksProps } from "./DrawerLinks.types";
import { dashboardLinksIconMapper } from "lib/icons";
import MegaMenuContent from "components/MegaMenuContent/MegaMenuContent";
const DrawerLinks: React.FC<DrawerLinksProps> = ({ pages }) => {
  const [dropdownToggleVals, setDropdownToggleVals] = useState<{
    [key: string]: boolean;
  }>({});
  /**
   *
   * @param {String} key The unique key to toggle state for
   */
  const handleDrawerMenuToggler = (key: string) => {
    // Toggle the val
    let newVals = { ...dropdownToggleVals };
    newVals[key] = !newVals[key];
    // Set new vals
    setDropdownToggleVals(newVals);
    console.log(newVals);
  };
  const ExpandMoreIcon = dashboardLinksIconMapper["expandMore"];
  const ExpandLessIcon = dashboardLinksIconMapper["expandLess"];
  return (
    <List>
      {pages.map((item, index) => {
        return (
          <div key={index}>
            {item?.subMenus || item?.megaMenuContent ? (
              <>
                <ListItem
                  button
                  key={item.title}
                  component="a"
                  onClick={() => {
                    handleDrawerMenuToggler(item.title);
                  }}
                >
                  <ListItemText primary={item.title} />
                  {dropdownToggleVals[item.title] ? (
                    <ExpandLessIcon />
                  ) : (
                    <ExpandMoreIcon />
                  )}
                </ListItem>
                <Collapse
                  in={dropdownToggleVals[item.title]}
                  timeout="auto"
                  key={index}
                  unmountOnExit
                >
                  {item?.megaMenuContent && (
                    <MegaMenuContent content={item.megaMenuContent!} />
                  )}
                  {item?.subMenus && (
                    <List component="div" disablePadding>
                      {item.subMenus.map((subItem, index) => {
                        return (
                          <Linked to={subItem.pathname} key={index}>
                            <ListItem
                              button
                              component="a"
                              sx={{
                                paddingLeft: (theme) => theme.spacing(4),
                              }}
                            >
                              <ListItemText primary={subItem.title} />
                            </ListItem>
                          </Linked>
                        );
                      })}
                    </List>
                  )}
                </Collapse>
              </>
            ) : (
              <Linked to={item.pathname || ""} key={index}>
                <ListItem button key={item.title} component="div">
                  <ListItemText primary={item.title} />
                </ListItem>
              </Linked>
            )}
          </div>
        );
      })}
    </List>
  );
};
export default DrawerLinks;
