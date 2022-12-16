// Generated with util/create-component.js
export type SubMenuItem = {
  title: string;
  pathname: string;
};
export type MenuItem = {
  title: string;
  pathname?: string;
  subMenus?: SubMenuItem[];
};

export interface DropdownMenuItemProps {
  menuItem: MenuItem;
  menuShowingDropdown: string;
  setMenuShowingDropdown: (menuTitle: string) => void;
}
