import { MegaMenuContent } from "components/MegaMenuContent/MegaMenuContent.types";
// Generated with util/create-component.js
export type SubMenuItem = {
  /**
   * The title to be displayed in the dropdown.
   */
  title: string;
  /**
   * The pathname to be used in the link.
   */
  pathname: string;
  /**
   * The description to be displayed below the option title
   */
  description?: string;
};
export type MenuItem = {
  /**
   * The title to be displayed in the dropdown.
   */
  title: string;
  /**
   * The pathname to be used in the link.
   */
  pathname?: string;
  /**
   * The sub menu items to be displayed in the dropdown.
   * If this is not provided, the dropdown will not be displayed.
   */
  subMenus?: SubMenuItem[];
  /**
   * Mega menu content sections
   */
  megaMenuContent?: MegaMenuContent;
  /**
   * The type of menu item. This is used to determine the type of dropdown to be displayed. E.g megamenu
   */
  type?: string;
};

export interface DropdownMenuItemProps {
  menuItem: MenuItem;
  menuShowingDropdown: string;
  setMenuShowingDropdown: (menuTitle: string) => void;
}
